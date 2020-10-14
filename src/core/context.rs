use super::{
    super::{One, Zero},
    Type,
};
use dyn_clone::{clone_trait_object, DynClone};
use std::fmt::Write;
pub trait Resolve: DynClone {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;
}

clone_trait_object!(<R> Resolve<Result = R>);

pub trait Simplify {
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result;
}

pub trait Simplificable: Resolve + Simplify {}

clone_trait_object!(<X> Simplificable<Result = X>);

pub trait Itertraitor: Iterator + DynClone {}

clone_trait_object!(<T> Itertraitor<Item = T>);

impl<I> Itertraitor for I where I: Iterator + Clone {}

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
pub enum Context<T, F> {
    Add(
        Box<dyn Itertraitor<Item = Type<Box<dyn Simplificable<Result = T>>>>>,
        F,
    ),
    Mul(
        Box<dyn Itertraitor<Item = Type<Box<dyn Simplificable<Result = T>>>>>,
        F,
    ),
}

impl<T, R, F> Resolve for Context<T, F>
where
    T: Clone,
    R: One
        + Zero
        + Clone
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
    F: Fn(T) -> R + Clone,
{
    type Result = R;
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
}

impl<T, F> Context<T, F> {
    pub fn resolve<R>(self) -> R
    where
        T: Clone,
        R: One
            + Zero
            + Clone
            + std::ops::Mul
            + std::ops::Add
            + std::ops::Div<Output = R>
            + std::ops::Sub<Output = R>,
        F: Fn(T) -> R + Clone,
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
    pub fn map<P, R>(&self, f: P) -> R
    where
        P: Fn(&Box<dyn Itertraitor<Item = Type<Box<dyn Simplificable<Result = T>>>>>, &F) -> R,
    {
        match self {
            Context::Add(iter, func) => f(iter, func),
            Context::Mul(iter, func) => f(iter, func),
        }
    }
}

impl<T, F> Simplify for Context<T, F> {
    // remove func
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

impl<T, R, F> Simplificable for Context<T, F>
where
    T: Clone,
    R: One
        + Zero
        + Clone
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
    F: Fn(T) -> R + Clone,
{
}

fn product<I, V, X, R>(iter: I, func: fn(X) -> R) -> Context<X, fn(X) -> R>
where
    I: Iterator<Item = Type<V>> + Clone + 'static,
    V: Simplificable<Result = X> + 'static,
{
    Context::Mul(
        Box::new(
            iter.map(|item| item.map(|val| Box::new(val) as Box<dyn Simplificable<Result = _>>)),
        ),
        func,
    )
}

fn sum<I, V, X, R>(iter: I, func: fn(X) -> R) -> Context<X, fn(X) -> R>
where
    I: Iterator<Item = Type<V>> + Clone + 'static,
    V: Simplificable<Result = X> + 'static,
{
    Context::Add(
        Box::new(
            iter.map(|item| item.map(|val| Box::new(val) as Box<dyn Simplificable<Result = _>>)),
        ),
        func,
    )
}

impl<T, R, F> std::ops::Div<Context<T, F>> for Context<T, F>
where
    T: Clone + 'static,
    R: One
        + Zero
        + Clone
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>
        + 'static,
    F: Fn(T) -> R + Clone + 'static,
{
    type Output = Context<R, fn(R) -> R>;
    fn div(self, rhs: Context<T, F>) -> Self::Output {
        product(
            vec![Type::Normal(self), Type::Inverse(rhs)].into_iter(),
            |x| x,
        )
    }
}

impl<T, R, F> std::ops::Mul<Context<T, F>> for Context<T, F>
where
    T: Clone + 'static,
    R: One
        + Zero
        + Clone
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>
        + 'static,
    F: Fn(T) -> R + Clone + 'static,
{
    type Output = Context<R, fn(R) -> R>;
    fn mul(self, rhs: Context<T, F>) -> Self::Output {
        product(
            vec![Type::Normal(self), Type::Normal(rhs)].into_iter(),
            |x| x,
        )
    }
}

impl<T, R, F> std::ops::Add<Context<T, F>> for Context<T, F>
where
    T: Clone + 'static,
    R: One
        + Zero
        + Clone
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>
        + 'static,
    F: Fn(T) -> R + Clone + 'static,
{
    type Output = Context<R, fn(R) -> R>;
    fn add(self, rhs: Context<T, F>) -> Self::Output {
        sum(
            vec![Type::Normal(self), Type::Normal(rhs)].into_iter(),
            |x| x,
        )
    }
}

impl<T, R, F> std::ops::Sub<Context<T, F>> for Context<T, F>
where
    T: Clone + 'static,
    R: One
        + Zero
        + Clone
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>
        + 'static,
    F: Fn(T) -> R + Clone + 'static,
{
    type Output = Context<R, fn(R) -> R>;
    fn sub(self, rhs: Context<T, F>) -> Self::Output {
        sum(
            vec![Type::Normal(self), Type::Inverse(rhs)].into_iter(),
            |x| x,
        )
    }
}

pub fn main() {
    // (1 * 2) + 1 + (1 + 2)
    let a = sum(
        vec![
            Type::Normal(product(
                vec![Type::Normal(1), Type::Normal(2)].into_iter(),
                |x| x,
            )),
            Type::Normal(sum(std::iter::once(Type::Normal(1)), |x| x)),
            Type::Normal(sum(
                vec![Type::Normal(1), Type::Normal(2)].into_iter(),
                |x| x,
            )),
        ]
        .into_iter(),
        |x| x,
    );
    println!(
        "{}",
        a.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", a.resolve());

    // (1 + (1 * 2) + (1 + 2 + 3) + (1 * 2 * 3 * (1 + 2 + 3 + 4)) + (1 + 2 + 3 + 4 + 5))
    let b = sum(
        (1..=5).map(|val| {
            if val % 2 == 0 {
                Type::Normal(product(
                    (1..=val).map(|val| {
                        if val % 4 == 0 {
                            Type::Normal(sum((1..=val).map(|val| Type::Normal(val)), |x| x))
                        } else {
                            Type::Normal(sum(std::iter::once(Type::Normal(val)), |x| x))
                        }
                    }),
                    |x| x,
                ))
            } else if val == 1 {
                Type::Normal(sum(std::iter::once(Type::Normal(val)), |x| x))
            } else {
                Type::Normal(sum((1..=val).map(|val| Type::Normal(val)), |x| x))
            }
        }),
        |x| x,
    );
    println!(
        "{}",
        b.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", b.resolve());

    // 10
    let c = product(vec![Type::Normal(10)].into_iter(), |x| x);
    println!(
        "{}",
        c.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", c.resolve());

    // 1/10
    let d = product(vec![Type::Inverse(10.0)].into_iter(), |x| x);
    println!(
        "{}",
        d.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", d.resolve());

    // 10
    let e = sum(vec![Type::Normal(10)].into_iter(), |x| x);
    println!(
        "{}",
        e.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", e.resolve());

    // -10
    let f = sum(vec![Type::Inverse(10)].into_iter(), |x| x);
    println!(
        "{}",
        f.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", f.resolve());

    // (10 / 5)
    let g = product(vec![Type::Normal(10), Type::Inverse(5)].into_iter(), |x| x);
    println!(
        "{}",
        g.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", g.resolve());

    // 10 * (1/5) * 10 * (1/5) * 10 * (1/5)
    // (10 * 10 * 10) / (5 * 5 * 5)
    let h = product(
        vec![
            Type::Normal(10),
            Type::Inverse(5),
            Type::Normal(10),
            Type::Inverse(5),
            Type::Normal(10),
            Type::Inverse(5),
        ]
        .into_iter(),
        |x| x,
    );
    println!(
        "{}",
        h.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", h.resolve());

    let i = sum(
        vec![Type::Inverse(5), Type::Inverse(5), Type::Inverse(5)].into_iter(),
        |x| x,
    );
    println!(
        "{}",
        i.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", i.resolve());

    let j = sum(
        vec![
            Type::Normal(15),
            Type::Inverse(5),
            Type::Inverse(5),
            Type::Inverse(5),
        ]
        .into_iter(),
        |x| x,
    );
    println!(
        "{}",
        j.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", j.resolve());

    let k = sum(
        vec![
            Type::Normal(sum(std::iter::once(Type::Inverse(15)), |x| x)),
            Type::Inverse(sum(std::iter::once(Type::Normal(10)), |x| x)),
        ]
        .into_iter(),
        |x| x,
    );
    println!(
        "{}",
        k.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", k.resolve());

    // ops tests
    println!("\n---ops test---");

    let val = product(vec![Type::Normal(10)].into_iter(), |x| x);

    println!(
        "val1 := {}",
        val.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {}", val.clone().resolve());
    println!(
        "val2 := {}",
        val.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {}", val.clone().resolve());

    println!("--------------");
    let div = val.clone() / val.clone();
    println!("div := val1 / val2");
    println!(
        "div := {}",
        div.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {}", div.resolve());
    println!("--------------");
    let mul = val.clone() * val.clone();
    println!("mul := val1 * val2");
    println!(
        "mul := {}",
        mul.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {}", mul.resolve());
    println!("--------------");
    let add = val.clone() + val.clone();
    println!("add := val1 + val2");
    println!(
        "add := {}",
        add.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {}", add.resolve());
    println!("--------------");
    let sub = val.clone() - val.clone();
    println!("sub := val1 - val2");
    println!(
        "sub := {}",
        sub.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {}", sub.resolve());
    println!("--------------");
}
