#![feature(step_trait)]

pub trait Zero: Sized + std::ops::Add<Self, Output = Self> {
    fn zero() -> Self;
}
pub trait One: Sized + std::ops::Mul<Self, Output = Self> {
    fn one() -> Self;
}

macro_rules! bulk_impl_traits {
  ($type:ty, $zero:expr, $one:expr) => {
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
  (($($type:ty),+) => ($zero:expr, $one:expr)) => {
      $(bulk_impl_traits!($type, $zero, $one);)+
  };
}

bulk_impl_traits!((i8, i16, i32, i64, isize) => (0, 1));
bulk_impl_traits!((u8, u16, u32, u64, usize) => (0, 1));
bulk_impl_traits!((f32, f64) => (0.0, 1.0));
#[cfg(has_i128)]
bulk_impl_traits!((i128, u128) => (0, 1));

#[inline]
pub fn sigma<T, R>(start: T, end: T, func: impl Fn(T) -> R) -> R
where
    T: std::iter::Step,
    R: std::iter::Sum,
{
    (start..=end).map(func).sum()
}

#[inline]
pub fn product<T, R>(min: T, max: T, func: impl Fn(T) -> R) -> R
where
    T: std::iter::Step,
    R: std::iter::Product,
{
    (min..=max).map(func).product()
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_sigma() {
        assert_eq!(sigma(0, 0, |x| x), 0);
        assert_eq!(sigma(1, 1, |x| x), 1);
        assert_eq!(sigma(1, 10, |x| x), 55);
        assert_eq!(sigma(1, 10, |x| u32::pow(x, 2)), 385);
    }
    #[test]
    fn test_product() {
        assert_eq!(product(0, 0, |x| x), 0);
        assert_eq!(product(1, 1, |x| x), 1);
        assert_eq!(product(1, 10, |x| x), 3628800);
        assert_eq!(product(1, 10, |x| u64::pow(x, 2)), 13168189440000);
    }
}
