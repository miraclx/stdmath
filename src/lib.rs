#![feature(step_trait)]
#[inline]
pub fn sigma<T, R>(start: T, end: T, func: impl Fn(T) -> R) -> R
where
    T: std::iter::Step,
    R: std::iter::Sum,
{
    (start..=end).map(func).sum()
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
}
