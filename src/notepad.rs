use dyn_clone::{clone_trait_object, DynClone};
use std::fmt::Write;
use stdmath::{One, Zero};

#[derive(Debug, Clone)]
pub enum Context1<R> {
    Add(Vec<Context1<R>>),
    Mul(Vec<Context1<R>>),
    Nil(R),
}

impl<R> Context1<R> {
    pub fn resolve(self) -> R
    where
        R: Zero + One,
    {
        let (items, is_additive) = match self {
            Context1::Add(items) => (items, true),
            Context1::Mul(items) => (items, false),
            Context1::Nil(val) => return val,
        };
        items
            .into_iter()
            .fold(None, |prev, item| {
                let val = item.resolve();
                let result = match prev {
                    Some(prev) => {
                        if is_additive {
                            prev + val
                        } else {
                            prev * val
                        }
                    }
                    None => val,
                };
                Some(result)
            })
            .unwrap_or_else(|| if is_additive { R::zero() } else { R::one() })
    }
    pub fn repr_into(self, file: &mut dyn Write) -> std::fmt::Result
    where
        R: std::fmt::Debug,
    {
        let (items, is_additive) = match self {
            Context1::Add(items) => (items, true),
            Context1::Mul(items) => (items, false),
            Context1::Nil(val) => return write!(file, "{:?}", val),
        };
        write!(file, "(")?;
        for (index, item) in items.into_iter().enumerate() {
            write!(
                file,
                "{}",
                if index != 0 {
                    if is_additive {
                        " + "
                    } else {
                        " * "
                    }
                } else {
                    ""
                }
            )?;
            item.repr_into(file)?;
        }
        write!(file, ")")
    }
    pub fn repr(self) -> Result<String, std::fmt::Error>
    where
        R: std::fmt::Debug,
    {
        let mut file = String::new();
        self.repr_into(&mut file)?;
        Ok(file)
    }
}

pub fn cx1() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context1::Add(vec![
        Context1::Mul(vec![Context1::Nil(1), Context1::Nil(2)]),
        Context1::Nil(1),
        Context1::Add(vec![Context1::Nil(1), Context1::Nil(2)]),
    ]);
    println!(
        "{}",
        a.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = Context1::Add(
        (1..=5)
            .map(|val| {
                if val % 2 == 0 {
                    Context1::Mul(
                        (1..=val)
                            .map(|val| {
                                if val % 4 == 0 {
                                    Context1::Add(
                                        (1..=val).map(|val| Context1::Nil(val)).collect::<Vec<_>>(),
                                    )
                                } else {
                                    Context1::Nil(val)
                                }
                            })
                            .collect::<Vec<_>>(),
                    )
                } else if val == 1 {
                    Context1::Nil(val)
                } else {
                    Context1::Add((1..=val).map(|val| Context1::Nil(val)).collect::<Vec<_>>())
                }
            })
            .collect::<Vec<_>>(),
    );
    println!(
        "{}",
        b.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", b.resolve());
}

pub enum Context2<R> {
    Add(Box<dyn Iterator<Item = Context2<R>>>),
    Mul(Box<dyn Iterator<Item = Context2<R>>>),
    Nil(R),
}

impl<R> Context2<R> {
    pub fn resolve(self) -> R
    where
        R: Zero + One,
    {
        let (items, is_additive) = match self {
            Context2::Add(items) => (items, true),
            Context2::Mul(items) => (items, false),
            Context2::Nil(val) => return val,
        };
        items
            .fold(None, |prev, item| {
                let val = item.resolve();
                let result = match prev {
                    Some(prev) => {
                        if is_additive {
                            prev + val
                        } else {
                            prev * val
                        }
                    }
                    None => val,
                };
                Some(result)
            })
            .unwrap_or_else(|| if is_additive { R::zero() } else { R::one() })
    }
}

pub fn cx2() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context2::<u8>::Add(Box::new(
        vec![
            Context2::Mul(Box::new(
                vec![Context2::Nil(1), Context2::Nil(2)].into_iter(),
            )),
            Context2::Nil(1),
            Context2::Add(Box::new(
                vec![Context2::Nil(1), Context2::Nil(2)].into_iter(),
            )),
        ]
        .into_iter(),
    ));
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = Context2::Add(Box::new((1..=5).map(|val| {
        if val % 2 == 0 {
            Context2::Mul(Box::new((1..=val).map(|val| {
                if val % 4 == 0 {
                    Context2::Add(Box::new((1..=val).map(|val| Context2::Nil(val))))
                } else {
                    Context2::Nil(val)
                }
            })))
        } else if val == 1 {
            Context2::Nil(val)
        } else {
            Context2::Add(Box::new((1..=val).map(|val| Context2::Nil(val))))
        }
    })));
    println!(" = {}", b.resolve());
}

pub trait Resolve: DynClone {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;
}

clone_trait_object!(<R> Resolve<Result = R>);

macro_rules! bulk_impl_traits {
    ($($type:ty),+) => {
        $(
            impl Resolve for $type {
                type Result = $type;
                #[inline]
                fn resolve(self: Box<Self>) -> Self::Result {
                    *self
                }
            }
        )+
    };
}

bulk_impl_traits!(i8, i16, i32, i64, isize);
bulk_impl_traits!(u8, u16, u32, u64, usize);
bulk_impl_traits!(f32, f64);
bulk_impl_traits!(i128, u128);

#[derive(Clone)]
pub enum Context3<R> {
    Add(Vec<Box<dyn Resolve<Result = R>>>),
    Mul(Vec<Box<dyn Resolve<Result = R>>>),
    Nil(Box<dyn Resolve<Result = R>>),
}

impl<R> Resolve for Context3<R>
where
    R: One + Zero + Clone,
{
    type Result = R;
    fn resolve(self: Box<Self>) -> Self::Result {
        match *self {
            Context3::Mul(val) => val.into_iter().fold(R::one(), |a, i| a * i.resolve()),
            Context3::Add(val) => val.into_iter().fold(R::zero(), |a, i| a + i.resolve()),
            Context3::Nil(val) => val.resolve(),
        }
    }
}

impl<R> Context3<R> {
    pub fn resolve(self) -> R
    where
        R: One + Zero + Clone,
    {
        Resolve::resolve(Box::new(self))
    }
}

fn cx3() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context3::Add(vec![
        Box::new(Context3::Mul(vec![
            Box::new(Context3::Nil(Box::new(1))),
            Box::new(Context3::Nil(Box::new(2))),
        ])),
        Box::new(Context3::Nil(Box::new(1))),
        Box::new(Context3::Add(vec![
            Box::new(Context3::Nil(Box::new(1))),
            Box::new(Context3::Nil(Box::new(2))),
        ])),
    ]);
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = Context3::Add(
        (1..=5)
            .map(|val| {
                if val % 2 == 0 {
                    Box::new(Context3::Mul(
                        (1..=val)
                            .map(|val| {
                                (if val % 4 == 0 {
                                    Box::new(Context3::Add(
                                        (1..=val)
                                            .map(|val| {
                                                Box::new(Context3::Nil(Box::new(val)))
                                                    as Box<dyn Resolve<Result = _>>
                                            })
                                            .collect::<Vec<_>>(),
                                    ))
                                } else {
                                    Box::new(Context3::Nil(Box::new(val)))
                                }) as Box<dyn Resolve<Result = _>>
                            })
                            .collect::<Vec<_>>(),
                    ))
                } else if val == 1 {
                    Box::new(Context3::Nil(Box::new(val)))
                } else {
                    Box::new(Context3::Add(
                        (1..=val)
                            .map(|val| {
                                Box::new(Context3::Nil(Box::new(val)))
                                    as Box<dyn Resolve<Result = _>>
                            })
                            .collect::<Vec<_>>(),
                    ))
                }
            } as Box<dyn Resolve<Result = _>>)
            .collect::<Vec<_>>(),
    );
    println!(" = {}", b.resolve());
}

#[derive(Clone)]
pub enum Context4<T, R> {
    Add(Vec<Box<dyn Resolve<Result = T>>>, fn(T) -> R),
    Mul(Vec<Box<dyn Resolve<Result = T>>>, fn(T) -> R),
    Nil(Box<dyn Resolve<Result = T>>, fn(T) -> R),
}

impl<T, R> Resolve for Context4<T, R>
where
    T: Clone,
    R: One + Zero + Clone,
{
    type Result = R;
    fn resolve(self: Box<Self>) -> Self::Result {
        match *self {
            Context4::Mul(val, func) => {
                val.into_iter().fold(R::one(), |a, i| a * func(i.resolve()))
            }
            Context4::Add(val, func) => val
                .into_iter()
                .fold(R::zero(), |a, i| a + func(i.resolve())),
            Context4::Nil(val, func) => func(val.resolve()),
        }
    }
}

impl<T, R> Context4<T, R> {
    pub fn resolve(self) -> R
    where
        T: Clone,
        R: One + Zero + Clone,
    {
        Resolve::resolve(Box::new(self))
    }
}

fn cx4() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context4::Add(
        vec![
            Box::new(Context4::Mul(
                vec![
                    Box::new(Context4::Nil(Box::new(1), |x| x)),
                    Box::new(Context4::Nil(Box::new(2), |x| x)),
                ],
                |x| x,
            )),
            Box::new(Context4::Nil(Box::new(1), |x| x)),
            Box::new(Context4::Add(
                vec![
                    Box::new(Context4::Nil(Box::new(1), |x| x)),
                    Box::new(Context4::Nil(Box::new(2), |x| x)),
                ],
                |x| x,
            )),
        ],
        |x| x,
    );
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = Context4::Add(
        (1..=5)
            .map(|val| {
                if val % 2 == 0 {
                    Box::new(Context4::Mul(
                        (1..=val)
                            .map(|val| {
                                (if val % 4 == 0 {
                                    Box::new(Context4::Add(
                                        (1..=val)
                                            .map(|val| {
                                                Box::new(Context4::Nil(Box::new(val), |x| x))
                                                    as Box<dyn Resolve<Result = _>>
                                            })
                                            .collect::<Vec<_>>(),
                                        |x| x,
                                    ))
                                } else {
                                    Box::new(Context4::Nil(Box::new(val), |x| x))
                                }) as Box<dyn Resolve<Result = _>>
                            })
                            .collect::<Vec<_>>(),
                        |x| x,
                    ))
                } else if val == 1 {
                    Box::new(Context4::Nil(Box::new(val), |x| x))
                } else {
                    Box::new(Context4::Add(
                        (1..=val)
                            .map(|val| {
                                Box::new(Context4::Nil(Box::new(val), |x| x))
                                    as Box<dyn Resolve<Result = _>>
                            })
                            .collect::<Vec<_>>(),
                        |x| x,
                    ))
                }
            } as Box<dyn Resolve<Result = _>>)
            .collect::<Vec<_>>(),
        |x| x,
    );
    println!(" = {}", b.resolve());
}

pub trait Itertraitor: Iterator + DynClone {}

clone_trait_object!(<T> Itertraitor<Item = T>);

impl<I> Itertraitor for I where I: Iterator + Clone {}

#[derive(Clone)]
pub enum Context5<T, R> {
    Add(
        Box<dyn Itertraitor<Item = Box<dyn Resolve<Result = T>>>>,
        fn(T) -> R,
    ),
    Mul(
        Box<dyn Itertraitor<Item = Box<dyn Resolve<Result = T>>>>,
        fn(T) -> R,
    ),
    Nil(Box<dyn Resolve<Result = T>>, fn(T) -> R),
}

impl<T, R> Resolve for Context5<T, R>
where
    T: Clone,
    R: One + Zero + Clone,
{
    type Result = R;
    fn resolve(self: Box<Self>) -> Self::Result {
        match *self {
            Context5::Mul(val, func) => val.fold(R::one(), |a, i| a * func(i.resolve())),
            Context5::Add(val, func) => val.fold(R::zero(), |a, i| a + func(i.resolve())),
            Context5::Nil(val, func) => func(val.resolve()),
        }
    }
}

impl<T, R> Context5<T, R> {
    pub fn resolve(self) -> R
    where
        T: Clone,
        R: One + Zero + Clone,
    {
        Resolve::resolve(Box::new(self))
    }
}

fn cx5() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context5::Add(
        Box::new(
            vec![
                Box::new(Context5::Mul(
                    Box::new(
                        vec![
                            Box::new(Context5::Nil(Box::new(1), |x| x))
                                as Box<dyn Resolve<Result = _>>,
                            Box::new(Context5::Nil(Box::new(2), |x| x))
                                as Box<dyn Resolve<Result = _>>,
                        ]
                        .into_iter(),
                    ) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                )) as Box<dyn Resolve<Result = _>>,
                Box::new(Context5::Nil(Box::new(1), |x| x)) as Box<dyn Resolve<Result = _>>,
                Box::new(Context5::Add(
                    Box::new(
                        vec![
                            Box::new(Context5::Nil(Box::new(1), |x| x))
                                as Box<dyn Resolve<Result = _>>,
                            Box::new(Context5::Nil(Box::new(2), |x| x))
                                as Box<dyn Resolve<Result = _>>,
                        ]
                        .into_iter(),
                    ) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                )) as Box<dyn Resolve<Result = _>>,
            ]
            .into_iter(),
        ) as Box<dyn Itertraitor<Item = _>>,
        |x| x,
    );
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = Context5::Add(
        Box::new((1..=5).map(|val| {
            if val % 2 == 0 {
                Box::new(Context5::Mul(
                    Box::new((1..=val).map(|val| {
                        (if val % 4 == 0 {
                            Box::new(Context5::Add(
                                Box::new((1..=val).map(|val| {
                                    Box::new(Context5::Nil(Box::new(val), |x| x))
                                        as Box<dyn Resolve<Result = _>>
                                }))
                                    as Box<dyn Itertraitor<Item = _>>,
                                |x| x,
                            ))
                        } else {
                            Box::new(Context5::Nil(Box::new(val), |x| x))
                        }) as Box<dyn Resolve<Result = _>>
                    })) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                ))
            } else if val == 1 {
                Box::new(Context5::Nil(Box::new(val), |x| x))
            } else {
                Box::new(Context5::Add(
                    Box::new((1..=val).map(|val| {
                        Box::new(Context5::Nil(Box::new(val), |x| x))
                            as Box<dyn Resolve<Result = _>>
                    })) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                ))
            }
        } as Box<dyn Resolve<Result = _>>)) as Box<dyn Itertraitor<Item = _>>,
        |x| x,
    );
    println!(" = {}", b.resolve());
}

pub fn product<I: Iterator, X, R>(iter: I, func: fn(X) -> R) -> Context5<X, R>
where
    I: Clone,
    I: 'static,
    I::Item: Resolve<Result = X>,
{
    Context5::Mul(
        Box::new(iter.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>)),
        func,
    )
}
pub fn sum<I: Iterator, X, R>(iter: I, func: fn(X) -> R) -> Context5<X, R>
where
    I: Clone,
    I: 'static,
    I::Item: Resolve<Result = X>,
{
    Context5::Add(
        Box::new(iter.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>)),
        func,
    )
}

pub trait Simplify {
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result;
}

pub trait Simplificable: Resolve + Simplify {}

clone_trait_object!(<X> Simplificable<Result = X>);

macro_rules! bulk_impl_traits {
    ($($type:ty),+) => {
        $(
            impl Simplify for $type
            where
                $type: std::fmt::Debug
            {
                #[inline]
                fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
                    write!(file, "{:?}", self)
                }
            }
            impl Simplificable for $type {}
        )+
    };
}

bulk_impl_traits!(i8, i16, i32, i64, isize);
bulk_impl_traits!(u8, u16, u32, u64, usize);
bulk_impl_traits!(f32, f64);
bulk_impl_traits!(i128, u128);

#[derive(Clone)]
pub enum Context6<T, R> {
    Add(
        Box<dyn Itertraitor<Item = Box<dyn Simplificable<Result = T>>>>,
        fn(T) -> R,
    ),
    Mul(
        Box<dyn Itertraitor<Item = Box<dyn Simplificable<Result = T>>>>,
        fn(T) -> R,
    ),
    Nil(Box<dyn Simplificable<Result = T>>, fn(T) -> R),
}

impl<T, R> Resolve for Context6<T, R>
where
    T: Clone,
    R: One + Zero + Clone,
{
    type Result = R;
    fn resolve(self: Box<Self>) -> Self::Result {
        match *self {
            Context6::Mul(val, func) => val.fold(R::one(), |a, i| a * func(i.resolve())),
            Context6::Add(val, func) => val.fold(R::zero(), |a, i| a + func(i.resolve())),
            Context6::Nil(val, func) => func(val.resolve()),
        }
    }
}

impl<T, R> Context6<T, R> {
    pub fn resolve(self) -> R
    where
        T: Clone,
        R: One + Zero + Clone,
    {
        Resolve::resolve(Box::new(self))
    }
    pub fn repr_into(self, file: &mut dyn Write) -> std::fmt::Result {
        Simplify::simplify(Box::new(self), file)
    }
    pub fn repr(self) -> Result<String, std::fmt::Error> {
        let mut file = String::new();
        self.repr_into(&mut file)?;
        Ok(file)
    }
}

impl<T, R> Simplify for Context6<T, R> {
    // remove func
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
        let (iter, is_additive) = match *self {
            Context6::Add(iter, _) => (iter, true),
            Context6::Mul(iter, _) => (iter, false),
            Context6::Nil(val, _) => return val.simplify(file),
        };
        write!(file, "(")?;
        for (index, item) in iter.enumerate() {
            write!(
                file,
                "{}",
                if index != 0 {
                    if is_additive {
                        " + "
                    } else {
                        " * "
                    }
                } else {
                    ""
                }
            )?;
            Simplify::simplify(item, file)?;
        }
        write!(file, ")")
    }
}

impl<T, R> Simplificable for Context6<T, R>
where
    T: Clone,
    R: One + Zero + Clone,
{
}

fn cx6() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context6::Add(
        Box::new(
            vec![
                Box::new(Context6::Mul(
                    Box::new(
                        vec![
                            Box::new(Context6::Nil(Box::new(1), |x| x))
                                as Box<dyn Simplificable<Result = _>>,
                            Box::new(Context6::Nil(Box::new(2), |x| x))
                                as Box<dyn Simplificable<Result = _>>,
                        ]
                        .into_iter(),
                    ) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                )) as Box<dyn Simplificable<Result = _>>,
                Box::new(Context6::Nil(Box::new(1), |x| x)) as Box<dyn Simplificable<Result = _>>,
                Box::new(Context6::Add(
                    Box::new(
                        vec![
                            Box::new(Context6::Nil(Box::new(1), |x| x))
                                as Box<dyn Simplificable<Result = _>>,
                            Box::new(Context6::Nil(Box::new(2), |x| x))
                                as Box<dyn Simplificable<Result = _>>,
                        ]
                        .into_iter(),
                    ) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                )) as Box<dyn Simplificable<Result = _>>,
            ]
            .into_iter(),
        ) as Box<dyn Itertraitor<Item = _>>,
        |x| x,
    );
    println!(
        "{}",
        a.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = Context6::Add(
        Box::new((1..=5).map(|val| {
            if val % 2 == 0 {
                Box::new(Context6::Mul(
                    Box::new((1..=val).map(|val| {
                        (if val % 4 == 0 {
                            Box::new(Context6::Add(
                                Box::new((1..=val).map(|val| {
                                    Box::new(Context6::Nil(Box::new(val), |x| x))
                                        as Box<dyn Simplificable<Result = _>>
                                }))
                                    as Box<dyn Itertraitor<Item = _>>,
                                |x| x,
                            ))
                        } else {
                            Box::new(Context6::Nil(Box::new(val), |x| x))
                        }) as Box<dyn Simplificable<Result = _>>
                    })) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                ))
            } else if val == 1 {
                Box::new(Context6::Nil(Box::new(val), |x| x))
            } else {
                Box::new(Context6::Add(
                    Box::new((1..=val).map(|val| {
                        Box::new(Context6::Nil(Box::new(val), |x| x))
                            as Box<dyn Simplificable<Result = _>>
                    })) as Box<dyn Itertraitor<Item = _>>,
                    |x| x,
                ))
            }
        } as Box<dyn Simplificable<Result = _>>)) as Box<dyn Itertraitor<Item = _>>,
        |x| x,
    );
    println!(
        "{}",
        b.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", b.resolve());
}

pub fn main() {
    println!("[\x1b[32mContext 1\x1b[0m] (\x1b[33mVec<Context>, Repr, Cloneable\x1b[0m)");
    cx1();
    println!("[\x1b[32mContext 2\x1b[0m] (\x1b[33mBox<dyn Iterator<Item = Context>>, Non-repr, Non-cloneable\x1b[0m)");
    cx2();
    println!(
        "[\x1b[32mContext 3\x1b[0m] (\x1b[33mVec<Box<dyn Resolve>>, Non-repr, Clonable\x1b[0m)"
    );
    cx3();
    println!(
        "[\x1b[32mContext 4\x1b[0m] (\x1b[33mVec<Box<dyn Resolve>>, Non-repr, Clonable, Transforming\x1b[0m)"
    );
    cx4();
    println!(
        "[\x1b[32mContext 5\x1b[0m] (\x1b[33mBox<dyn Iterator<Item = Box<dyn Resolve>>>, Non-repr, Clonable, Transforming\x1b[0m)"
    );
    cx5();
    println!(
        "[\x1b[32mContext 6\x1b[0m] (\x1b[33mBox<dyn Iterator<Item = Box<dyn Resolve>>>, Repr, Clonable, Transforming\x1b[0m)"
    );
    cx6();
}
