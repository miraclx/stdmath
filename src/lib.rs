#![feature(step_trait)]

pub mod core;
pub mod exclude;

#[cfg(feature = "concurrency")]
use rayon::prelude::*;

#[cfg(feature = "num_traits")]
mod traits {
    pub use num::traits::{One, Pow, Zero};
}

#[cfg(not(feature = "num_traits"))]
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

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_factorial() {
        let val = factorial(5);
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );
        assert_eq!(val.resolve(), 120);
    }
    #[test]
    fn test_op() {
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
}
