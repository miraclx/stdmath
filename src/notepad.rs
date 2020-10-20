use super::{
    core::{Flippable, Type},
    exclude::ExcludedIteratorExt,
    One, Zero,
};
use std::{
    any::Any,
    cmp::{Eq, Ordering, PartialEq},
    fmt::{self, Debug, Write},
    hash::{Hash, Hasher},
};

pub trait Simplify {
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result;
}

pub trait Resolve: Simplify {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;

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

enum Identity {
    Add,
    Mul,
    Nil,
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
        #[inline]
        fn as_any(&self) -> &dyn Any {
            self
        }
        stage_default_methods!($($rest)*);
    };
    (_cmp $($rest:tt)*) => {
        #[inline]
        fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering> {
            other
                .as_any()
                .downcast_ref::<Self>()
                .map_or(None, |other| PartialOrd::partial_cmp(self, other))
        }
        stage_default_methods!($($rest)*);
    };
    (_debug $($rest:tt)*) => {
        #[inline]
        fn _debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            Debug::fmt(self, f)
        }
        stage_default_methods!($($rest)*);
    };
    (_clone $($rest:tt)*) => {
        #[inline]
        fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
            Box::new(self.clone()) as Box<dyn Resolve<Result = Self::Result>>
        }
        stage_default_methods!($($rest)*);
    };
    (_hash $($rest:tt)*) => {
        #[inline]
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
        }
        impl Simplify for $type {
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

impl<T: 'static, X> Resolve for Box<T>
where
    T: Resolve<Result = X> + Clone + Hash + Debug + PartialOrd,
{
    type Result = X;
    stage_default_methods!(ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        (*self).resolve()
    }
}

impl<T> Simplify for Box<T>
where
    T: Simplify,
{
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
        (*self).simplify(file)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, PartialOrd)]
pub enum Context<R> {
    Add(Vec<Type<Box<dyn Resolve<Result = R>>>>),
    Mul(Vec<Type<Box<dyn Resolve<Result = R>>>>),
}

impl<R: 'static> std::ops::Add for Context<R>
where
    R: Clone + Hash + Debug + PartialOrd,
    R: One
        + Zero
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
{
    type Output = Context<R>;
    fn add(self, rhs: Self) -> Self::Output {
        let mut res = vec![];
        match (self.is_additive(), rhs.is_additive()) {
            // todo: check if results are the same
            // todo: dont merge if types don't match
            (true, true) => {
                // method 1
                // both are additive
                // merge both into an additive context

                // lets resolve this well enough to not need a vec
                res.extend(
                    self.dump()
                        .into_iter()
                        .exclude(rhs.dump().into_iter().flip())
                        .include_overflow_with(|item| item.flip()),
                );
            }
            (true, false) => {
                // method 2
                // only I am additive
                // extend res with self's contents
                // push rhs as is into res

                res.extend(
                    self.dump()
                        .into_iter()
                        .exclude(
                            std::iter::once(Type::Normal(
                                Box::new(rhs) as Box<dyn Resolve<Result = R>>
                            ))
                            .flip(),
                        )
                        .include_overflow_with(|item| item.flip()),
                );
            }
            (false, true) => {
                // method 2
                // only rhs is additive
                // push self as is into res
                // extend res with rhs's contents

                res.extend(
                    std::iter::once(Type::Normal(Box::new(self) as Box<dyn Resolve<Result = R>>))
                        .exclude(rhs.dump().into_iter().flip())
                        .include_overflow_with(|item| item.flip()),
                )
            }
            _ => {
                // method 3
                // anything else
                // push both self and rhs into an additive context

                res.push(Type::Normal(Box::new(self)));
                res.push(Type::Normal(Box::new(rhs)));
            }
        };
        Context::Add(res)
    }
}

impl<R: 'static> Context<R> {
    fn resolve(self) -> R
    where
        R: Clone + Hash + Debug + PartialOrd,
        //
        R: One
            + Zero
            + std::ops::Mul
            + std::ops::Add
            + std::ops::Div<Output = R>
            + std::ops::Sub<Output = R>,
    {
        Box::new(self).resolve()
    }
    pub fn repr_into(self, file: &mut dyn Write) -> std::fmt::Result {
        Simplify::simplify(Box::new(self), file)
    }
    pub fn repr(self) -> Result<String, std::fmt::Error> {
        let mut file = String::new();
        self.repr_into(&mut file)?;
        Ok(file)
    }
    fn dump(self) -> Vec<Type<Box<dyn Resolve<Result = R>>>> {
        match self {
            Context::Add(vec) => vec,
            Context::Mul(vec) => vec,
        }
    }
    pub fn is_additive(&self) -> bool {
        if let Context::Add(_) = self {
            return true;
        }
        false
    }
}

impl<R: 'static> Resolve for Context<R>
where
    R: Clone + Hash + Debug + PartialOrd,
    //
    R: One
        + Zero
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
{
    type Result = R;
    stage_default_methods!(ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        let (vec, default, [normal_op, inverse_op]): (_, fn() -> R, [fn(R, R) -> R; 2]) =
            match *self {
                Context::Add(vec) => (vec, || R::zero(), [std::ops::Add::add, std::ops::Sub::sub]),
                Context::Mul(vec) => (vec, || R::one(), [std::ops::Mul::mul, std::ops::Div::div]),
            };
        let (mut normal, mut inverse) = (None, None);
        for item in vec {
            let is_inverted = item.is_inverted();
            let this = if !is_inverted {
                &mut normal
            } else {
                &mut inverse
            };
            let val = item.unwrap().resolve();
            *this = Some(match this.take() {
                Some(prev) => normal_op(prev, val),
                None => val,
            })
        }
        let normal = normal.unwrap_or_else(default);
        let inverse = inverse.unwrap_or_else(default);

        inverse_op(normal, inverse)
    }
}

impl<R: 'static> Simplify for Context<R> {
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
        let (is_additive, vec) = (self.is_additive(), self.dump());
        let (mut normal, mut inverse) = (None, None);
        for item in vec {
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

pub fn sum<I, T, X>(iter: I) -> Context<X>
where
    I: IntoIterator<Item = Type<T>>,
    T: Resolve<Result = X> + 'static,
{
    Context::Add(
        iter.into_iter()
            .map(|item| item.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>))
            .collect(),
    )
}

pub fn mul<I, T, X>(iter: I) -> Context<X>
where
    I: IntoIterator<Item = Type<T>>,
    T: Resolve<Result = X> + 'static,
{
    Context::Mul(
        iter.into_iter()
            .map(|item| item.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>))
            .collect(),
    )
}

pub fn main() {
    let a = sum(vec![
        Type::Normal(mul(vec![Type::Normal(10)])),
        Type::Normal(mul(vec![Type::Normal(10), Type::Normal(13)])),
    ]);
    println!(
        "{:?}",
        a.clone().repr().expect("failed to represent math context")
    );
    println!(" = {:?}", a.resolve());

    let val1 = sum(vec![
        Type::Normal(mul(vec![Type::Normal(10)])),
        Type::Normal(mul(vec![Type::Normal(10), Type::Normal(13)])),
    ]);
    let val2 = mul(vec![
        Type::Normal(sum(vec![Type::Normal(10)])),
        Type::Normal(sum(vec![Type::Normal(10), Type::Normal(13)])),
    ]);

    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // test addition method 1
    //  merge two contexts if both match the operation
    //  i.e two additive contexts are merged with an additive operation

    // Example
    //  input:
    //   (5 - 10 - 6) + (-10 + 5 + 6)
    //  1: exclude inverse matches and merge
    //   (5 - 10 - 10 + 5)
    //  2: group variants
    //   (5 + 5) - (10 + 10)
    //  result:
    //   -10
    let val1 = sum(vec![Type::Normal(5), Type::Inverse(10), Type::Inverse(6)]);
    let val2 = sum(vec![Type::Inverse(10), Type::Normal(5), Type::Normal(6)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // test addition method 2
    //  include a side as-is into the result if the variant of the context
    //  doesn't conform to the operation
    //  i.e adding a mul context to an add will include the mul as an
    //      item within the add context
    //    > add[n(a), i(b)] + mul[n(c), i(d)]
    //    = add[n(a), i(b), n(mul[n(c), i(d)])]
    //    > mul[n(a), i(b)] + add[n(c), i(b)]
    //    = mul[n(a), i(b), n(add[n(c), i(b)])]

    // Example 1:
    //  input:
    //   (2 + 3) + (4 * 5)
    //  1: exclude rhs from lhs if present else merge rhs into lhs
    //   (2 + 3 + (4 * 5))
    //  2: group variants
    //   (2 + 3 + (4 * 5))
    //  result:
    //   25
    let val1 = sum(vec![Type::Normal(2), Type::Normal(3)]);
    let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // Example 2:
    //  input:
    //   (2 * 3) + (4 + 5)
    //  1: exclude lhs from rhs if present else merge lhs into rhs
    //   ((2 * 3) + 4 + 5)
    //  2: group variants
    //   ((2 * 3) + 4 + 5)
    //  result:
    //   15
    let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
    let val2 = sum(vec![Type::Normal(4), Type::Normal(5)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // test addition method 3
    //  include both sides into the result as-is if they dont match the op
    //  i.e adding a mul context to a mul will include both as-is into the result
    //    > mul[ n(a), i(b) ] + mul[ n(c), i(d) ]
    //    = add[
    //        n(mul[ n(a), i(b) ]),
    //        n(mul[ n(c), i(d) ])
    //      ]

    // Example
    //  input:
    //   (2 * 3) + (4 * 5)
    //  1: exclude rhs from lhs if present else merge rhs into lhs
    //   ((2 * 3) + (4 * 5))
    //  2: group variants
    //   ((2 * 3) + (4 * 5))
    //  result:
    //   26
    let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
    let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn basic_sum_repr() {
        let val = sum((3..=6).map(|item| Type::Normal(item)));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(3 + 4 + 5 + 6)"
        );
    }
    #[test]
    fn basic_mul_repr() {
        let val = mul((4..=7).map(|item| Type::Normal(item)));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(4 * 5 * 6 * 7)"
        );
    }
    #[test]
    fn basic_sum_compute() {
        let val = sum((3..=6).map(|item| Type::Normal(item)));
        assert_eq!(val.resolve(), 18);
    }
    #[test]
    fn basic_mul_compute() {
        let val = mul((4..=7).map(|item| Type::Normal(item)));
        assert_eq!(val.resolve(), 840);
    }
    #[test]
    fn trait_clone() {
        let val = sum((9..=12).map(|item| Type::Normal(item)));
        assert_eq!(
            val.clone()
                .repr()
                .expect("failed to represent math context"),
            "(9 + 10 + 11 + 12)"
        );
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(9 + 10 + 11 + 12)"
        );
    }
    #[test]
    fn basic_repr_compute() {
        let val = mul((1..=10).map(|item| Type::Normal(item)));
        assert_eq!(
            val.clone()
                .repr()
                .expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10)"
        );
        assert_eq!(val.resolve(), 3628800);
    }
    #[test]
    fn context_add_method_1() {
        // (1 - 2 + 3) + (-1 + 2 - 3)
        // ? 1: exclude inverse matches and merge
        //  (1 - 2 + 3 - 1 + 2 - 3)
        // ? 2: group variants
        //  (1 + 3 + 2) - (2 + 1 + 3)
        // ? result:
        //  0
        let val1 = sum(vec![Type::Normal(1), Type::Inverse(2), Type::Normal(3)]);
        let val2 = sum(vec![Type::Inverse(1), Type::Normal(2), Type::Inverse(3)]);
        let val3 = val1 + val2;
        assert_eq!(
            val3.clone()
                .repr()
                .expect("failed to represent math context"),
            "((1 + 3 + 2) - (2 + 1 + 3))"
        );
        assert_eq!(val3.resolve(), 0);
    }
    #[test]
    fn context_add_method_2a() {
        // (2 + 3) + (4 * 5)
        // ? 1: exclude rhs from lhs if present else merge rhs into lhs
        //  (2 + 3 + (4 * 5))
        // ? 2: group variants
        //  (2 + 3 + (4 * 5))
        // ? result:
        //  25
        let val1 = sum(vec![Type::Normal(2), Type::Normal(3)]);
        let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
        let val3 = val1 + val2;
        assert_eq!(
            val3.clone()
                .repr()
                .expect("failed to represent math context"),
            "(2 + 3 + (4 * 5))"
        );
        assert_eq!(val3.resolve(), 25);
    }
    #[test]
    fn context_add_method_2b() {
        // (2 * 3) + (4 + 5)
        // ? 1: exclude rhs from lhs if present else merge rhs into lhs
        //  ((2 * 3) + (4 + 5))
        // ? 2: group variants
        //  ((2 * 3) + 4 + 5)
        // ? result:
        //  15
        let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
        let val2 = sum(vec![Type::Normal(4), Type::Normal(5)]);
        let val3 = val1 + val2;
        assert_eq!(
            val3.clone()
                .repr()
                .expect("failed to represent math context"),
            "((2 * 3) + 4 + 5)"
        );
        assert_eq!(val3.resolve(), 15);
    }
    #[test]
    fn context_add_method_3() {
        // (2 * 3) + (4 * 5)
        // ? 1: exclude rhs from lhs if present else merge rhs into lhs
        //  ((2 * 3) + (4 * 5))
        // ? 2: group variants
        //  ((2 * 3) + (4 * 5))
        // ? result:
        //  26
        let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
        let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
        let val3 = val1 + val2;
        assert_eq!(
            val3.clone()
                .repr()
                .expect("failed to represent math context"),
            "((2 * 3) + (4 * 5))"
        );
        assert_eq!(val3.resolve(), 26);
    }
}
