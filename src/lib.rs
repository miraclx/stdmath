#![feature(step_trait)]

pub mod core;
pub mod exclude;

mod traits {
    /// Trait for pow-supported numbers.
    pub trait Pow<RHS> {
        type Output;
        fn pow(self, exp: RHS) -> Self::Output;
    }

    /// Defines a additive identity element for Self.
    pub trait Zero:
        Sized + std::ops::Add<Self, Output = Self> + std::ops::Sub<Self, Output = Self>
    {
        fn zero() -> Self;
    }

    /// Defines a multiplicative identity element for Self.
    pub trait One:
        Sized + std::ops::Mul<Self, Output = Self> + std::ops::Div<Self, Output = Self>
    {
        fn one() -> Self;
    }

    macro_rules! bulk_impl_traits {
        (@ $type:ty, $zero:expr, $one:expr) => {
            impl Zero for $type {
                #[inline]
                fn zero() -> Self {
                    $zero
                }
            }
            impl One for $type {
                #[inline]
                fn one() -> Self {
                    $one
                }
            }
        };
        ($type:ty, $zero:expr, $one:expr) => {
            bulk_impl_traits!(@ $type, $zero, $one);
            impl Pow<u32> for $type {
                type Output = Self;
                #[inline]
                fn pow(self, exp: u32) -> Self {
                    <$type>::pow(self, exp)
                }
            }
        };
        (($($type:ty),+) => ($zero:expr, $one:expr)) => {
            $(bulk_impl_traits!($type, $zero, $one);)+
        };
        (@ ($($type:ty),+) => ($zero:expr, $one:expr)) => {
            $(bulk_impl_traits!(@ $type, $zero, $one);)+
        };
    }

    bulk_impl_traits!((i8, i16, i32, i64, isize) => (0, 1));
    bulk_impl_traits!((u8, u16, u32, u64, usize) => (0, 1));
    bulk_impl_traits!(@ (f32, f64) => (0.0, 1.0));
    bulk_impl_traits!((i128, u128) => (0, 1));
}

pub use self::core::{mul, sum, Context, Resolve, Simplify, Type};
pub use traits::{One, Pow, Zero};

pub fn factorial<T: One + Resolve + 'static>(val: T) -> Context<T::Result>
where
    std::ops::RangeInclusive<T>: Iterator<Item = T>,
{
    mul(Type::Normal(T::one()..=val))
}

#[derive(Debug, Hash, Clone, PartialEq, PartialOrd)]
pub struct Factorial<T>(pub T);

impl<T: One + Resolve + 'static> Factorial<T> {
    pub fn resolve(self) -> T::Result
    where
        T: Clone + std::hash::Hash + PartialOrd + std::fmt::Display + std::fmt::Debug,
        T::Result: One + Zero + std::ops::Mul + std::ops::Add + std::ops::Div + std::ops::Sub,
        std::ops::RangeInclusive<T>: Iterator<Item = T>,
    {
        Resolve::resolve(Box::new(self))
    }
}

impl<T: std::fmt::Display> Simplify for Factorial<T> {
    fn simplify(&self, file: &mut dyn std::fmt::Write) -> std::fmt::Result {
        write!(file, "{}!", self.0)
    }
}

impl<T: One + Resolve + 'static> Resolve for Factorial<T>
where
    T: Clone + std::hash::Hash + PartialOrd + std::fmt::Display + std::fmt::Debug,
    T::Result: One + Zero + std::ops::Mul + std::ops::Add + std::ops::Div + std::ops::Sub,
    std::ops::RangeInclusive<T>: Iterator<Item = T>,
{
    type Result = T::Result;
    stage_default_methods!(is_friendly_with_all ALL);
    fn to_context(self) -> Context<Self::Result> {
        mul(Type::Normal(T::one()..=self.0))
    }
    fn resolve(self: Box<Self>) -> Self::Result {
        self.to_context().resolve()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_factorial() {
        let val = Factorial(20u64);
        assert_eq!(val.repr().expect("failed to represent math context"), "20!");
        assert_eq!(val.resolve(), 2432902008176640000);
    }
    #[test]
    fn test_op_gt() {
        let val1 = factorial(5);
        assert_eq!(
            val1.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );

        let val2 = factorial(3);
        assert_eq!(
            val2.repr().expect("failed to represent math context"),
            "(1 * 2 * 3)"
        );

        let res = val1 / val2;
        assert_eq!(
            res.repr().expect("failed to represent math context"),
            "(4 * 5)"
        );

        assert_eq!(res.resolve(), 20);
    }
    #[test]
    fn test_op_eq() {
        let val1 = factorial(5);
        assert_eq!(
            val1.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );

        let val2 = factorial(5);
        assert_eq!(
            val2.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );

        let res = val1 / val2;
        assert_eq!(res.repr().expect("failed to represent math context"), "");

        assert_eq!(res.resolve(), 1);
    }
    #[test]
    fn test_op_lt() {
        let val1 = factorial(3);
        assert_eq!(
            val1.repr().expect("failed to represent math context"),
            "(1 * 2 * 3)"
        );

        let val2 = factorial(5);
        assert_eq!(
            val2.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );

        let res = val1 / val2;
        assert_eq!(
            res.repr().expect("failed to represent math context"),
            "1/(4 * 5)"
        );

        assert_eq!(res.resolve(), 20);
    }
}
