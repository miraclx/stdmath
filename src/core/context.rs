use super::{
    super::{One, Zero},
    Type,
};
use std::{
    any::Any,
    cmp::{Eq, Ordering, PartialEq},
    fmt::{self, Debug, Write},
    hash::{Hash, Hasher},
};

pub trait Resolve {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result;

    // methods needed for dynamicism
    fn as_any(&self) -> &dyn Any;
    fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering>;
    fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
        unimplemented!()
    }
    fn _debug(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
    fn _hash(&self, _state: &mut dyn Hasher) {
        unimplemented!()
    }
}

impl<X> PartialEq<dyn Resolve<Result = X>> for dyn Resolve<Result = X> {
    fn eq(&self, other: &dyn Resolve<Result = X>) -> bool {
        if let Some(Ordering::Equal) = self._cmp(other) {
            return true;
        }
        false
    }
}

impl<X> Eq for dyn Resolve<Result = X> {}

impl<X> PartialOrd<dyn Resolve<Result = X>> for dyn Resolve<Result = X> {
    fn partial_cmp(&self, other: &dyn Resolve<Result = X>) -> Option<Ordering> {
        self._cmp(other)
    }
}

impl<X> Debug for dyn Resolve<Result = X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._debug(f)
    }
}

impl<X> Clone for Box<dyn Resolve<Result = X>> {
    fn clone(&self) -> Self {
        self._clone()
    }
}

impl<X> Hash for Box<dyn Resolve<Result = X>> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self._hash(state);
    }
}

macro_rules! stage_default_methods {
    () => {};
    (ALL) => {
        stage_default_methods!(as_any _cmp _debug _clone _hash);
    };
    (as_any $($rest:tt)*) => {
        fn as_any(&self) -> &dyn Any {
            self
        }
        stage_default_methods!($($rest)*);
    };
    (_cmp $($rest:tt)*) => {
        fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering> {
            other
                .as_any()
                .downcast_ref::<Self>()
                .map_or(None, |other| PartialOrd::partial_cmp(self, other))
        }
        stage_default_methods!($($rest)*);
    };
    (_debug $($rest:tt)*) => {
        fn _debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            Debug::fmt(self, f)
        }
        stage_default_methods!($($rest)*);
    };
    (_clone $($rest:tt)*) => {
        fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
            Box::new(self.clone()) as Box<dyn Resolve<Result = Self::Result>>
        }
        stage_default_methods!($($rest)*);
    };
    (_hash $($rest:tt)*) => {
        fn _hash(&self, mut state: &mut dyn Hasher) {
            self.hash(&mut state)
        }
        stage_default_methods!($($rest)*);
    };
}

macro_rules! bulk_impl_traits {
    (@ [$($methods:tt)+] $type:ty) => {
        impl Resolve for $type {
            type Result = $type;
            stage_default_methods!($($methods)+);
            #[inline]
            fn resolve(self: Box<Self>) -> Self::Result {
                *self
            }
            #[inline]
            fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
                write!(file, "{:?}", self)
            }
        }
    };
    (nohash($($type:ty),+)) => {
        $(bulk_impl_traits!(@ [as_any _cmp _debug _clone] $type);)+
    };
    ($($type:ty),+) => {
        $(bulk_impl_traits!(@ [ALL] $type);)+
    }
}

bulk_impl_traits!(i8, i16, i32, i64, isize);
bulk_impl_traits!(u8, u16, u32, u64, usize);
bulk_impl_traits!(nohash(f32, f64));
bulk_impl_traits!(i128, u128);

#[derive(Clone, Hash, Debug, PartialEq, PartialOrd)]
pub enum Context<T, F> {
    Add(Vec<Type<Box<dyn Resolve<Result = T>>>>, F),
    Mul(Vec<Type<Box<dyn Resolve<Result = T>>>>, F),
}

impl<T, R, F> Resolve for Context<T, F>
where
    T: Clone,
    R: One
        + Zero
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
    F: Fn(T) -> R + Clone,
    // FIXME: can these be unbounded? or at least custom defined
    T: 'static,
    F: 'static,
    // TODO: look into these
    T: Hash + Debug + PartialOrd,
    F: Hash + Debug + PartialOrd,
{
    type Result = R;
    stage_default_methods!(ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        let (iter, func, default, [normal_op, inverse_op]): (_, _, fn() -> R, [fn(R, R) -> R; 2]) =
            match *self {
                Context::Add(iter, func) => (
                    iter,
                    func,
                    || R::zero(),
                    [std::ops::Add::add, std::ops::Sub::sub],
                ),
                Context::Mul(iter, func) => (
                    iter,
                    func,
                    || R::one(),
                    [std::ops::Mul::mul, std::ops::Div::div],
                ),
            };
        let (mut normal, mut inverse) = (None, None);
        for item in iter {
            let is_inverted = item.is_inverted();
            let this = if !is_inverted {
                &mut normal
            } else {
                &mut inverse
            };
            let val = item.unwrap().resolve();
            *this = Some(match this.take() {
                Some(prev) => normal_op(prev, func(val)),
                None => func(val),
            })
        }
        let normal = normal.unwrap_or_else(default);
        let inverse = inverse.unwrap_or_else(default);

        inverse_op(normal, inverse)
    }
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
        let (iter, is_additive) = match *self {
            Context::Add(iter, _) => (iter, true),
            Context::Mul(iter, _) => (iter, false),
        };
        let (mut normal, mut inverse) = (None, None);
        for item in iter {
            let is_inverted = item.is_inverted();
            let this = if !is_inverted {
                &mut normal
            } else {
                &mut inverse
            };
            let mut file = String::new();
            item.unwrap().simplify(&mut file)?;
            if let Some((prev, over_one)) = this {
                *over_one = true;
                String::push_str(prev, if is_additive { " + " } else { " * " });
                String::push_str(prev, &file);
            } else {
                *this = Some((file, false));
            };
        }
        match (normal, inverse) {
            (Some((normal, n_over_one)), Some((inverse, f_over_one))) => write!(
                file,
                "({}{}{})",
                if n_over_one {
                    format!("({})", normal)
                } else {
                    normal
                },
                if is_additive { " - " } else { " / " },
                if f_over_one {
                    format!("({})", inverse)
                } else {
                    inverse
                },
            ),
            (Some((normal, n_over_one)), None) => {
                if n_over_one {
                    write!(file, "({})", normal)
                } else {
                    write!(file, "{}", normal)
                }
            }
            (None, Some((inverse, f_over_one))) => write!(
                file,
                "{}{}",
                if is_additive { "-" } else { "1/" },
                if f_over_one {
                    format!("({})", inverse)
                } else {
                    inverse
                }
            ),
            (None, None) => Ok(()),
        }
    }
}

impl<T, R, F> Context<T, F>
where
    T: Clone,
    R: One
        + Zero
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
    F: Fn(T) -> R + Clone,
    // FIXME: can these be unbounded? or at least custom defined
    T: 'static,
    F: 'static,
    // TODO: look into these
    T: Hash + Debug + PartialOrd,
    F: Hash + Debug + PartialOrd,
{
    pub fn resolve(self) -> R {
        Resolve::resolve(Box::new(self))
    }
    pub fn repr_into(self, file: &mut dyn Write) -> std::fmt::Result {
        Resolve::simplify(Box::new(self), file)
    }
    pub fn repr(self) -> Result<String, std::fmt::Error> {
        let mut file = String::new();
        self.repr_into(&mut file)?;
        Ok(file)
    }
    pub fn map<P>(&self, f: P) -> R
    where
        P: Fn(&Vec<Type<Box<dyn Resolve<Result = T>>>>, &F) -> R,
    {
        match self {
            Context::Add(iter, func) => f(iter, func),
            Context::Mul(iter, func) => f(iter, func),
        }
    }
    fn dump(self) -> (Vec<Type<Box<dyn Resolve<Result = T>>>>, F) {
        match self {
            Context::Add(iter, func) => (iter, func),
            Context::Mul(iter, func) => (iter, func),
        }
    }
    pub fn is_additive(&self) -> bool {
        if let Context::Add(_, _) = self {
            return true;
        }
        false
    }
}

fn product<I, V, X, R>(iter: I, func: fn(X) -> R) -> Context<X, fn(X) -> R>
where
    I: Iterator<Item = Type<V>> + Clone + 'static,
    V: Resolve<Result = X> + 'static,
{
    Context::Mul(
        iter.map(|item| item.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>))
            .collect::<Vec<_>>(),
        func,
    )
}

fn sum<I, V, X, R>(iter: I, func: fn(X) -> R) -> Context<X, fn(X) -> R>
where
    I: Iterator<Item = Type<V>> + Clone + 'static,
    V: Resolve<Result = X> + 'static,
{
    Context::Add(
        iter.map(|item| item.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>))
            .collect::<Vec<_>>(),
        func,
    )
}

pub fn main() {
    use super::{super::exclude::ExcludedIteratorExt, core::Flippable};
    let a = sum((1..=10).map(|val| Type::Normal(val)), |x| x);
    let b = sum((3..=6).map(|val| Type::Normal(val)), |x| x);
    let (vec1, _) = a.dump();
    let (vec2, _) = b.dump();

    // attempt inclusion (multiplication, addition)
    let c = vec1
        .iter()
        .cloned()
        .exclude(vec2.iter().cloned().flip())
        .include_overflow_with(|item| item.flip());
    println!("{:?}", c.collect::<Vec<_>>());

    // attempt exclusion (division, subtraction)
    let d = vec1
        .iter()
        .cloned()
        .exclude(vec2.iter().cloned())
        .include_overflow_with(|item| item.flip());
    println!("{:?}", d.collect::<Vec<_>>());
}

// impl<T, R, F> std::ops::Div<Context<T, F>> for Context<T, F>
// where
//     T: Clone + 'static,
//     R: One
//         + Zero
//         + Clone
//         + std::ops::Mul
//         + std::ops::Add
//         + std::ops::Div<Output = R>
//         + std::ops::Sub<Output = R>
//         + 'static,
//     F: Fn(T) -> R + Clone + 'static,
// {
//     type Output = Context<R, fn(R) -> R>;
//     fn div(self, rhs: Context<T, F>) -> Self::Output {
//         product(
//             vec![Type::Normal(self), Type::Inverse(rhs)].into_iter(),
//             |x| x,
//         )
//     }
// }

// impl<T, R, F> std::ops::Mul<Context<T, F>> for Context<T, F>
// where
//     T: Clone + 'static,
//     R: One
//         + Zero
//         + Clone
//         + std::ops::Mul
//         + std::ops::Add
//         + std::ops::Div<Output = R>
//         + std::ops::Sub<Output = R>
//         + 'static,
//     F: Fn(T) -> R + Clone + 'static,
// {
//     type Output = Context<R, fn(R) -> R>;
//     fn mul(self, rhs: Context<T, F>) -> Self::Output {
//         product(
//             vec![Type::Normal(self), Type::Normal(rhs)].into_iter(),
//             |x| x,
//         )
//     }
// }

// impl<T, R> std::ops::Add<Context<T, fn(T) -> R>> for Context<T, fn(T) -> R>
// where
//     T: Clone + 'static,
//     R: One
//         + Zero
//         + Clone
//         + std::ops::Mul
//         + std::ops::Add
//         + std::ops::Div<Output = R>
//         + std::ops::Sub<Output = R>
//         + 'static,
// {
//     type Output = Context<R, fn(R) -> R>;
//     fn add(self, rhs: Context<T, fn(T) -> R>) -> Self::Output {
//         let my_func = self.map(|_, func| func.clone());
//         let your_func = rhs.map(|_, func| func.clone());
//         match (self.is_additive(), rhs.is_additive(), my_func == your_func) {
//             (true, true, true) => {
//                 let (my_iter, _) = self.dump();
//                 let (your_iter, _) = rhs.dump();
//                 sum(
//                     std::iter::once(Type::Normal(Context::Add(
//                         Box::new(my_iter.chain(your_iter)),
//                         my_func,
//                     ))),
//                     |x| x,
//                 )
//             }
//             _ => sum(
//                 vec![Type::Normal(self), Type::Normal(rhs)].into_iter(),
//                 |x| x,
//             ),
//         }
//     }
// }

// impl<T, R, F> std::ops::Sub<Context<T, F>> for Context<T, F>
// where
//     T: Clone + 'static,
//     R: One
//         + Zero
//         + Clone
//         + std::ops::Mul
//         + std::ops::Add
//         + std::ops::Div<Output = R>
//         + std::ops::Sub<Output = R>
//         + 'static,
//     F: Fn(T) -> R + Clone + 'static,
// {
//     type Output = Context<R, fn(R) -> R>;
//     fn sub(self, rhs: Context<T, F>) -> Self::Output {
//         sum(
//             vec![Type::Normal(self), Type::Inverse(rhs)].into_iter(),
//             |x| x,
//         )
//     }
// }

// pub fn main() {
//     // (1 * 2) + 1 + (1 + 2)
//     let a = sum(
//         vec![
//             Type::Normal(product(
//                 vec![Type::Normal(1), Type::Normal(2)].into_iter(),
//                 |x| x,
//             )),
//             Type::Normal(sum(std::iter::once(Type::Normal(1)), |x| x)),
//             Type::Normal(sum(
//                 vec![Type::Normal(1), Type::Normal(2)].into_iter(),
//                 |x| x,
//             )),
//         ]
//         .into_iter(),
//         |x| x,
//     );
//     println!(
//         "{}",
//         a.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", a.resolve());

//     // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
//     let b = sum(
//         (1..=5).map(|val| {
//             if val % 2 == 0 {
//                 Type::Normal(product(
//                     (1..=val).map(|val| {
//                         if val % 4 == 0 {
//                             Type::Normal(sum((1..=val).map(|val| Type::Normal(val)), |x| x))
//                         } else {
//                             Type::Normal(sum(std::iter::once(Type::Normal(val)), |x| x))
//                         }
//                     }),
//                     |x| x,
//                 ))
//             } else if val == 1 {
//                 Type::Normal(sum(std::iter::once(Type::Normal(val)), |x| x))
//             } else {
//                 Type::Normal(sum((1..=val).map(|val| Type::Normal(val)), |x| x))
//             }
//         }),
//         |x| x,
//     );
//     println!(
//         "{}",
//         b.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", b.resolve());

//     // 10
//     let c = product(vec![Type::Normal(10)].into_iter(), |x| x);
//     println!(
//         "{}",
//         c.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", c.resolve());

//     // 1/10
//     let d = product(vec![Type::Inverse(10.0)].into_iter(), |x| x);
//     println!(
//         "{}",
//         d.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", d.resolve());

//     // 10
//     let e = sum(vec![Type::Normal(10)].into_iter(), |x| x);
//     println!(
//         "{}",
//         e.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", e.resolve());

//     // -10
//     let f = sum(vec![Type::Inverse(10)].into_iter(), |x| x);
//     println!(
//         "{}",
//         f.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", f.resolve());

//     // (10 / 5)
//     let g = product(vec![Type::Normal(10), Type::Inverse(5)].into_iter(), |x| x);
//     println!(
//         "{}",
//         g.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", g.resolve());

//     // 10 * (1/5) * 10 * (1/5) * 10 * (1/5)
//     // (10 * 10 * 10) / (5 * 5 * 5)
//     let h = product(
//         vec![
//             Type::Normal(10),
//             Type::Inverse(5),
//             Type::Normal(10),
//             Type::Inverse(5),
//             Type::Normal(10),
//             Type::Inverse(5),
//         ]
//         .into_iter(),
//         |x| x,
//     );
//     println!(
//         "{}",
//         h.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", h.resolve());

//     let i = sum(
//         vec![Type::Inverse(5), Type::Inverse(5), Type::Inverse(5)].into_iter(),
//         |x| x,
//     );
//     println!(
//         "{}",
//         i.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", i.resolve());

//     let j = sum(
//         vec![
//             Type::Normal(15),
//             Type::Inverse(5),
//             Type::Inverse(5),
//             Type::Inverse(5),
//         ]
//         .into_iter(),
//         |x| x,
//     );
//     println!(
//         "{}",
//         j.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", j.resolve());

//     let k = sum(
//         vec![
//             Type::Normal(sum(std::iter::once(Type::Inverse(15)), |x| x)),
//             Type::Inverse(sum(std::iter::once(Type::Normal(10)), |x| x)),
//         ]
//         .into_iter(),
//         |x| x,
//     );
//     println!(
//         "{}",
//         k.clone().repr().expect("failed to represent math context")
//     );
//     println!(" = {}", k.resolve());

//     // ops tests
//     println!("\n---ops test---");

//     let val = product(vec![Type::Normal(10)].into_iter(), |x| x);

//     println!(
//         "val1 := {}",
//         val.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", val.clone().resolve());
//     println!(
//         "val2 := {}",
//         val.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", val.clone().resolve());

//     println!("--------------");
//     let div = val.clone() / val.clone();
//     println!("div := val1 / val2");
//     println!(
//         "div := {}",
//         div.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", div.resolve());
//     println!("--------------");
//     let mul = val.clone() * val.clone();
//     println!("mul := val1 * val2");
//     println!(
//         "mul := {}",
//         mul.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", mul.resolve());
//     println!("--------------");
//     let add = val.clone() + val.clone();
//     println!("add := val1 + val2");
//     println!(
//         "add := {}",
//         add.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", add.resolve());
//     println!("--------------");
//     let sub = val.clone() - val.clone();
//     println!("sub := val1 - val2");
//     println!(
//         "sub := {}",
//         sub.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", sub.resolve());
//     println!("--------------");

//     // optimizing operations
//     println!("\n---optimization test---");

//     let func = |x| x;
//     let val1: Context<_, fn(i32) -> _> = Context::Add(
//         Box::new((1..=2).map(|v| Type::Normal(Box::new(v) as Box<dyn Simplificable<Result = _>>))),
//         func,
//     );
//     let val2: Context<_, fn(i32) -> _> = Context::Add(
//         Box::new((1..=2).map(|v| Type::Normal(Box::new(v) as Box<dyn Simplificable<Result = _>>))),
//         func,
//     );
//     let val3: Context<_, fn(i32) -> _> = Context::Add(
//         Box::new((1..=2).map(|v| Type::Normal(Box::new(v) as Box<dyn Simplificable<Result = _>>))),
//         |x| x,
//     );
//     let val4: Context<_, fn(i32) -> _> = Context::Add(
//         Box::new((1..=2).map(|v| Type::Normal(Box::new(v) as Box<dyn Simplificable<Result = _>>))),
//         |x| x,
//     );

//     println!(
//         "val1 := {} (func shared with val2)",
//         val1.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", val1.clone().resolve());
//     println!(
//         "val2 := {} (func shared with val1)",
//         val2.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", val2.clone().resolve());
//     println!(
//         "val3 := {} (unique func)",
//         val3.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", val3.clone().resolve());
//     println!(
//         "val4 := {} (unique func)",
//         val4.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", val4.clone().resolve());

//     println!("--------------");
//     let add = val1.clone() + val2.clone();
//     println!("add := val1 + val2");
//     println!(
//         "add := {}",
//         add.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", add.resolve());
//     let add = val3.clone() + val4.clone();
//     println!("add := val3 + val4");
//     println!(
//         "add := {}",
//         add.clone()
//             .repr()
//             .expect("failed to represent math context")
//     );
//     println!(" = {}", add.resolve());
//     println!("--------------");
// }
