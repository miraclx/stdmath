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
    pub trait Zero: Sized + std::ops::Add<Self, Output = Self> {
        fn zero() -> Self;
    }

    /// Defines a multiplicative identity element for Self.
    pub trait One: Sized + std::ops::Mul<Self, Output = Self> {
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
