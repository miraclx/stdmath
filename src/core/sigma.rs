use super::{
    super::{
        exclude::{ExcludedIterator, ExcludedIteratorExt},
        Zero,
    },
    core::*,
};
use std::hash::Hash;

#[derive(Clone)]
pub struct Sigma<I: Iterator, F> {
    iter: I,
    func: F,
}

pub type SigmaIntoIter<I> = DeBoxify<I>;

/// allows creating a Product value from an iterator of primitives
impl<'a, I, T: 'a, F, R> Sigma<TypedWithIter<TypedIter<I>>, F>
where
    I: Iterator<Item = T>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
{
    pub fn from_normal(iter: I, func: F) -> Self {
        Sigma::with(TypedIter::Normal(iter), func)
    }
    pub fn from_inverse(iter: I, func: F) -> Self {
        Sigma::with(TypedIter::Inverse(iter), func)
    }
}

impl<I, T, F, R> Sigma<TypedWithIter<I>, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
{
    pub fn with<P>(iter: P, func: F) -> Self
    where
        P: IntoIterator<Item = I::Item, IntoIter = I>,
    {
        Sigma {
            iter: TypedWithIter::new(iter.into_iter()),
            func,
        }
    }
}

impl<I, X, F> Sigma<I, F>
where
    I: Iterator<Item = Type<Box<dyn Resolve<Result = X>>>>,
{
    pub fn dump(self) -> I {
        self.iter
    }
}

impl<I, T, F, R> Sigma<I, F>
where
    I: Iterator<Item = Type<Box<T>>>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
    R: Zero + std::ops::Sub<Output = R>,
{
    pub fn compute(self) -> R {
        let func = &self.func;
        let (normal, inverse) = self.iter.fold((None, None), |(normal, inverse), val| {
            let is_inverted = val.is_inverted();
            let (this, other) = if !is_inverted {
                (normal, inverse)
            } else {
                (inverse, normal)
            };
            let this = Some(match this {
                Some(prev) => prev + func(val.unwrap().resolve()),
                None => func(val.unwrap().resolve()),
            });
            if !is_inverted {
                (this, other)
            } else {
                (other, this)
            }
        });
        let normal = normal.unwrap_or_else(|| R::zero());
        let inverse = inverse.unwrap_or_else(|| R::zero());

        normal - inverse
    }
}

impl<I, T, F, R> Resolve for Sigma<I, F>
where
    I: Iterator<Item = Type<Box<T>>>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
    R: Zero + std::ops::Sub<Output = R>,
{
    type Result = R;
    fn resolve(self: Box<Self>) -> Self::Result {
        self.compute()
    }
}

// converts a Sigma struct into an iterator of Type<T>
impl<I: Iterator<Item = Type<Box<T>>>, T, F> IntoIterator for Sigma<I, F> {
    type Item = Type<T>;
    type IntoIter = SigmaIntoIter<I>;
    fn into_iter(self) -> Self::IntoIter {
        SigmaIntoIter::new(self.iter)
    }
}

impl<B, C, T, F> std::ops::Sub<Sigma<C, F>> for Sigma<B, F>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator<Item = Type<Box<T>>>,
    T: Eq + Hash,
    Box<T>: Clone,
{
    type Output = Sigma<ExcludedIterator<B, C, Type<Box<T>>>, F>;
    fn sub(self, rhs: Sigma<C, F>) -> Self::Output {
        Sigma {
            iter: self
                .iter
                .exclude(rhs.iter)
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

impl<B, C, T, F> std::ops::Add<Sigma<C, F>> for Sigma<B, F>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator<Item = Type<Box<T>>>,
    T: Eq + Hash,
    Box<T>: Clone,
{
    type Output = Sigma<ExcludedIterator<B, FlippedIteratorOfTypes<C>, Type<Box<T>>>, F>;
    fn add(self, rhs: Sigma<C, F>) -> Self::Output {
        Sigma {
            iter: self
                .iter
                .exclude(rhs.iter.flip())
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn basic_compute() {
        // (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10)
        //  = 55

        let val = Sigma::from_normal(1..=10u8, |x| x);
        assert_eq!(val.compute(), 55);
    }
    #[test]
    fn custom_compute_add() {
        // (4 - 2) + (2 - 4)
        //  = 0

        let func = |x| x;
        let part1 = Sigma::with(vec![Type::Normal(4), Type::Inverse(2)], func);
        let part2 = Sigma::with(vec![Type::Normal(2), Type::Inverse(4)], func);
        let result = (part1 + part2).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 0);
    }
    #[test]
    fn custom_compute_sub() {
        // (4 - 2) - (2 - 4)
        //  = (4 + 4) - (2 + 2)
        //  = (8 - 4)
        //  = 4

        let func = |x| x;
        let part1 = Sigma::with(vec![Type::Normal(4), Type::Inverse(2)], func);
        let part2 = Sigma::with(vec![Type::Normal(2), Type::Inverse(4)], func);
        let mut result = (part1 - part2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(4),
                Type::Normal(4),
                Type::Inverse(2),
                Type::Inverse(2),
            ]
        );

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 4);
    }
    #[test]
    fn sub_compute() {
        // (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10) - (3 + 4 + 5 + 6)
        //  = (1 + 2 + 7 + 8 + 9 + 10)
        //  = 37

        let func = |x| x;
        let val1 = Sigma::from_normal(1..=10u8, func);
        let val2 = Sigma::from_normal(3..=6u8, func);
        let result = (val1 - val2).into_iter().collect::<Vec<_>>();

        assert_eq!(
            result,
            vec![
                Type::Normal(1),
                Type::Normal(2),
                Type::Normal(7),
                Type::Normal(8),
                Type::Normal(9),
                Type::Normal(10)
            ]
        );

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 37);
    }
    #[test]
    fn sub_overflow_compute() {
        // (3 + 4 + 5 + 6) - (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10)
        //  = 1 - (1 + 2 + 7 + 8 + 9 + 10)
        //  = -37

        let func = |x| x as i8;
        let val1 = Sigma::from_normal(1..=10u8, func);
        let val2 = Sigma::from_normal(3..=6u8, func);
        let mut result = (val2 - val1).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Inverse(1),
                Type::Inverse(2),
                Type::Inverse(7),
                Type::Inverse(8),
                Type::Inverse(9),
                Type::Inverse(10)
            ]
        );

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), -37);
    }
    #[test]
    fn sub_mixed_compute() {
        // (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10) - (6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15)
        //  = (1 + 2 + 3 + 4 + 5) - (11 + 12 + 13 + 14 + 15)
        //  = 0.000333000333000333

        let func = |x| x;
        let val1 = Sigma::from_normal(1..=10, func);
        let val2 = Sigma::from_normal(6..=15, func);
        let mut result = (val1 - val2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(1),
                Type::Normal(2),
                Type::Normal(3),
                Type::Normal(4),
                Type::Normal(5),
                Type::Inverse(11),
                Type::Inverse(12),
                Type::Inverse(13),
                Type::Inverse(14),
                Type::Inverse(15)
            ]
        );

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), -50);
    }
    #[test]
    fn sub_arbitrarily_compute() {
        // c = a + b = (1 + 2 + 3 + 4 + 5) - ((-1) + (-2) + (-3) + (-4) + (-5))
        // c =         (1 + 2 + 3 + 4 + 5 + 2 + 3 + 4 + 5)
        // d =         (1 + 2 + 3 + 4 + 5 + 1 + 2 + 3 + 4 + 5)
        // r = c - d = (1 + 2 + 3 + 4 + 5 + 2 + 3 + 4 + 5)
        //          : -(1 + 2 + 3 + 4 + 5 + 1 + 2 + 3 + 4 + 5)
        // r =         0

        let func = |x| x;
        let a = Sigma::with(TypedIter::Normal(1..=5), func);
        let b = Sigma::with(TypedIter::Inverse(1..=5), func);
        let c = a - b;
        let d = Sigma::from_normal((1..=5).chain(1..=5), func);
        let result = (c - d).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 0);
    }
    #[test]
    fn add_compute() {
        // (1 + 2 + 3 + 4 + 5) + (6 + 7 + 8 + 9 + 10)
        //  = 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10
        //  = 55

        let func = |x| x;
        let val1 = Sigma::from_normal(1..=5, func);
        let val2 = Sigma::from_normal(6..=10, func);
        let mut result = (val1 + val2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(1),
                Type::Normal(2),
                Type::Normal(3),
                Type::Normal(4),
                Type::Normal(5),
                Type::Normal(6),
                Type::Normal(7),
                Type::Normal(8),
                Type::Normal(9),
                Type::Normal(10)
            ]
        );

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 55);
    }
    #[test]
    fn add_overflow_compute() {
        // (3 + 4 + 5 + 6) + ((-3) + (-4) + (-5) + (-6) + (-7))
        //  = (3 + 4 + 5 + 6) - (3 + 4 + 5 + 6 + 7)
        //  = 0 - 7
        //  = -7

        let func = |x| x as i8;
        let val1 = Sigma::from_normal(3..=6, func);
        let val2 = Sigma::from_inverse(3..=7, func);
        let result = (val1 + val2).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![Type::Inverse(7)]);

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), -7);
    }
    #[test]
    fn add_mixed_compute() {
        // (6 + 7 + 8 + 9 + 10) + ((-3) + (-4) + (-5) + (-6) + (-7))
        //  = (6 + 7 + 8 + 9 + 10) - (3 + 4 + 5 + 6 + 7)
        //  = (8 + 9 + 10) - (3 + 4 + 5)
        //  = 15

        let func = |x| x;
        let val1 = Sigma::from_normal(6..=10, func);
        let val2 = Sigma::from_inverse(3..=7, func);
        let mut result = (val1 + val2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(8),
                Type::Normal(9),
                Type::Normal(10),
                Type::Inverse(3),
                Type::Inverse(4),
                Type::Inverse(5),
            ]
        );

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 15);
    }
    #[test]
    fn add_arbitrarily_compute() {
        // c = a + b = (1 + 2 + 3 + 4 + 5) + ((-6) + (-7) + (-8) + (-9) + (-10))
        // c =         (1 + 2 + 3 + 4 + 5) - (6 + 7 + 8 + 9 + 10)
        // d =         (6 + 7 + 8 + 9 + 10) + ((-1) + (-2) + (-3) + (-4) + (-5))
        // d =         (6 + 7 + 8 + 9 + 10) - (1 + 2 + 3 + 4 + 5)
        // r = c + d = ((1 + 2 + 3 + 4 + 5) - (6 + 7 + 8 + 9 + 10))
        //          : +((6 + 7 + 8 + 9 + 10) - (1 + 2 + 3 + 4 + 5))
        // r =         0

        let func = |x| x;
        let a = Sigma::with(TypedIter::Normal(1..=5), func);
        let b = Sigma::with(TypedIter::Inverse(6..=10), func);
        let c = a + b;
        let d = Sigma::with(
            TypedIter::Normal(6..=10).chain(TypedIter::Inverse(1..=5)),
            func,
        );
        let result = (c + d).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Sigma::with(result, func);
        assert_eq!(result.compute(), 0);
    }
}
