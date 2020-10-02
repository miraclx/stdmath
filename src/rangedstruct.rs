use std::hash::Hash;

use super::{
    exclude::{ExcludedIterator, ExcludedIteratorExt},
    One,
};

#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug, Ord, PartialOrd)]
pub enum Type<T> {
    Normal(T),
    Flipped(T),
}

impl<T> Type<T> {
    fn flip(self) -> Self {
        match self {
            Type::Normal(val) => Type::Flipped(val),
            Type::Flipped(val) => Type::Normal(val),
        }
    }
}

pub struct FlippedIteratorOfTypes<I: Iterator<Item = Type<T>>, T> {
    inner: I,
}

impl<I: Iterator<Item = Type<T>>, T> Iterator for FlippedIteratorOfTypes<I, T> {
    type Item = Type<T>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.flip())
    }
}

trait Flippable<I: Iterator<Item = Type<T>>, T> {
    fn flip(self) -> FlippedIteratorOfTypes<I, T>;
}

impl<I, T> Flippable<I, T> for I
where
    I: Iterator<Item = Type<T>>,
{
    fn flip(self) -> FlippedIteratorOfTypes<I, T> {
        FlippedIteratorOfTypes { inner: self }
    }
}

#[derive(Clone)]
pub enum TypedIter<I> {
    Normal(I),
    Flipped(I),
}

impl<I: Iterator<Item = T>, T> Iterator for TypedIter<I> {
    type Item = Type<T>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(match self {
            TypedIter::Normal(iter) => Type::Normal(iter.next()?),
            TypedIter::Flipped(iter) => Type::Flipped(iter.next()?),
        })
    }
}

#[derive(Clone)]
pub struct RangedStruct<I, F> {
    iter: I,
    func: F,
}

impl<I, T, F, R> RangedStruct<TypedIter<I>, F>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> R,
{
    pub fn from_normal(iter: I, func: F) -> Self {
        Self {
            iter: TypedIter::Normal(iter),
            func,
        }
    }
    pub fn from_flipped(iter: I, func: F) -> Self {
        Self {
            iter: TypedIter::Flipped(iter),
            func,
        }
    }
}

impl<I, T, F, R> RangedStruct<I, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(T) -> R,
{
    pub fn with<P>(iter: P, func: F) -> Self
    where
        P: IntoIterator<Item = Type<T>, IntoIter = I>,
    {
        RangedStruct {
            iter: iter.into_iter(),
            func,
        }
    }
    pub fn compute(self) -> R
    where
        R: One + std::ops::Div<Output = R> + std::iter::Product,
    {
        let func = &self.func;
        self.iter
            .map(|val| match val {
                Type::Normal(val) => func(val),
                Type::Flipped(val) => R::one() / func(val),
            })
            .product()
    }
}

impl<B, C, T, F> std::ops::Div<RangedStruct<C, F>> for RangedStruct<B, F>
where
    B: Iterator<Item = Type<T>>,
    C: Iterator<Item = Type<T>>,
    T: Eq + Hash,
{
    type Output = RangedStruct<ExcludedIterator<B, C, Type<T>>, F>;
    fn div(self, rhs: RangedStruct<C, F>) -> Self::Output {
        RangedStruct {
            iter: self
                .iter
                .exclude(rhs.iter)
                .with_transformer(|val| val)
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

impl<B, C, T, F> std::ops::Mul<RangedStruct<C, F>> for RangedStruct<B, F>
where
    B: Iterator<Item = Type<T>>,
    C: Iterator<Item = Type<T>>,
    T: Eq + Hash,
{
    type Output = RangedStruct<ExcludedIterator<B, FlippedIteratorOfTypes<C, T>, Type<T>>, F>;
    fn mul(self, rhs: RangedStruct<C, F>) -> Self::Output {
        RangedStruct {
            iter: self.iter.exclude(rhs.iter.flip()),
            func: self.func,
        }
    }
}

impl<I: Iterator, F> IntoIterator for RangedStruct<I, F> {
    type Item = I::Item;
    type IntoIter = I;
    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn type_flip() {
        let ty = Type::Normal(());
        assert_eq!(ty, Type::Normal(()));
        assert_ne!(ty, Type::Flipped(()));
        assert_eq!(ty.flip(), Type::Flipped(()));

        let ty = Type::Flipped(());
        assert_eq!(ty, Type::Flipped(()));
        assert_ne!(ty, Type::Normal(()));
        assert_eq!(ty.flip(), Type::Normal(()));
    }
    #[test]
    fn basic_compute() {
        let val = RangedStruct::from_normal(1..=10u8, |x| x as u32);
        assert_eq!(val.compute(), 3628800);
    }
    #[test]
    fn custom_compute_mul() {
        // (4 / 2) * (2 / 4) = 1
        let func = |x| x;
        let part1 = RangedStruct::with(vec![Type::Normal(4), Type::Flipped(2)], func);
        let part2 = RangedStruct::with(vec![Type::Normal(2), Type::Flipped(4)], func);
        let result = (part1 * part2).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = RangedStruct::with(result, func);
        assert_eq!(result.compute(), 1);
    }
    #[test]
    fn custom_compute_div() {
        // (4 / 2) / (2 / 4) = (4 * 4) / (2 * 2) = (16 / 4) = 4
        let func = |x| x as f64;
        let part1 = RangedStruct::with(vec![Type::Normal(4), Type::Flipped(2)], func);
        let part2 = RangedStruct::with(vec![Type::Normal(2), Type::Flipped(4)], func);
        let mut result = (part1 / part2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(4),
                Type::Normal(4),
                Type::Flipped(2),
                Type::Flipped(2),
            ]
        );

        let result = RangedStruct::with(result, func);
        assert_eq!(result.compute() as u8, 4);
    }
    #[test]
    fn div_compute() {
        // (10!) / (3 * 4 * 5 * 6)
        //  = (1 * 2 * 7 * 8 * 9 * 10)
        //  = 10080

        let func = |x| x as u16;
        let val1 = RangedStruct::from_normal(1..=10u8, func);
        let val2 = RangedStruct::from_normal(3..=6u8, func);
        let result = (val1 / val2).into_iter().collect::<Vec<_>>();

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

        let result = RangedStruct::with(result, func);
        assert_eq!(result.compute(), 10080);
    }
    #[test]
    fn div_overflow_compute() {
        // (3 * 4 * 5 * 6) / (10!)
        //  = 1 / (1 * 2 * 7 * 8 * 9 * 10)
        //  = 0.00000992063492063492

        let func = |x| x as f64;
        let val1 = RangedStruct::from_normal(1..=10u8, func);
        let val2 = RangedStruct::from_normal(3..=6u8, func);
        let mut result = (val2 / val1).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Flipped(1),
                Type::Flipped(2),
                Type::Flipped(7),
                Type::Flipped(8),
                Type::Flipped(9),
                Type::Flipped(10)
            ]
        );

        let result = RangedStruct::with(result, func);
        assert_eq!(result.compute(), 0.0000992063492063492);
    }
    #[test]
    fn div_mixed_compute() {
        let func = |x| x as f64;
        let val1 = RangedStruct::from_normal(1..=10, func);
        let val2 = RangedStruct::from_normal(6..=15, func);
        let mut result = (val1 / val2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(1),
                Type::Normal(2),
                Type::Normal(3),
                Type::Normal(4),
                Type::Normal(5),
                Type::Flipped(11),
                Type::Flipped(12),
                Type::Flipped(13),
                Type::Flipped(14),
                Type::Flipped(15)
            ]
        );

        let result = RangedStruct::with(result, func);
        assert_eq!(result.compute(), 0.000333000333000333);
    }
    #[test]
    fn div_arbitrarily_compute() {
        let func = |x| x;
        let a = RangedStruct::with(TypedIter::Normal(1..=5), func);
        let b = RangedStruct::with(TypedIter::Flipped(1..=5), func);
        let c = a / b;
        let d = RangedStruct::from_normal((1..=5).chain(1..=5), func);
        let e = c / d;
        let mut result = e.into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(result, vec![]);

        let result = RangedStruct::with(result, func);
        assert_eq!(result.compute(), 1);
    }
}
