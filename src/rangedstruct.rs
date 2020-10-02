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
    pub iter: I,
    func: F,
}

impl<I, T, F, R> RangedStruct<TypedIter<I>, F>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> R,
{
    pub fn new(iter: I, func: F) -> Self {
        Self {
            iter: TypedIter::Normal(iter),
            func,
        }
    }
}

impl<I, T, F, R> RangedStruct<I, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(T) -> R,
{
    pub fn with(iter: I, func: F) -> Self {
        RangedStruct { iter, func }
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
{
    type Output = RangedStruct<std::iter::Chain<B, C>, F>;
    fn mul(self, rhs: RangedStruct<C, F>) -> Self::Output {
        RangedStruct {
            iter: self.iter.chain(rhs.iter),
            func: self.func,
        }
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
        let val = RangedStruct::new(1..=10u8, |x| x as u32);
        assert_eq!(val.compute(), 3628800);
    }
    #[test]
    fn div_compute() {
        // (10!) / (3 * 4 * 5 * 6)
        //  = (1 * 2 * 7 * 8 * 9 * 10)
        //  = 10080

        let func = |x| x as u16;
        let val1 = RangedStruct::new(1..=10u8, func);
        let val2 = RangedStruct::new(3..=6u8, func);
        let result = (val1 / val2).iter.collect::<Vec<_>>();

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

        let result = RangedStruct::with(result.iter().cloned(), func);
        assert_eq!(result.compute(), 10080);
    }
    #[test]
    fn div_overflow_compute() {
        // (3 * 4 * 5 * 6) / (10!)
        //  = 1 / (1 * 2 * 7 * 8 * 9 * 10)
        //  = 0.00000992063492063492

        let func = |x| x as f64;
        let val1 = RangedStruct::new(1..=10u8, func);
        let val2 = RangedStruct::new(3..=6u8, func);
        let mut result = (val2 / val1).iter.collect::<Vec<_>>();

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

        let result = RangedStruct::with(result.iter().cloned(), func);
        assert_eq!(result.compute(), 0.0000992063492063492);
    }
    #[test]
    fn div_arbitrarily_compute() {
        let func = |x| x;
        let a = RangedStruct::with(TypedIter::Normal(1..=5), func);
        let b = RangedStruct::with(TypedIter::Flipped(1..=5), func);
        let c = a / b;
        let d = RangedStruct::new((1..=5).chain(1..=5), func);
        let e = c / d;
        let mut result = e.iter.collect::<Vec<_>>();

        result.sort();

        assert_eq!(result, vec![]);

        let result = RangedStruct::with(result.iter().cloned(), func);
        assert_eq!(result.compute(), 1);
    }
}
