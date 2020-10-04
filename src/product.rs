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
    fn is_flipped(&self) -> bool {
        match self {
            Type::Normal(_) => false,
            Type::Flipped(_) => true,
        }
    }
    fn unwrap(self) -> T {
        match self {
            Type::Normal(val) => val,
            Type::Flipped(val) => val,
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
pub struct Product<I, F> {
    iter: I,
    func: F,
}

impl<I, T, F, R> Product<TypedIter<I>, F>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> R,
{
    pub fn from_normal(iter: I, func: F) -> Self {
        Product::with(TypedIter::Normal(iter), func)
    }
    pub fn from_flipped(iter: I, func: F) -> Self {
        Product::with(TypedIter::Flipped(iter), func)
    }
}

impl<I, T, F, R> Product<I, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(T) -> R,
{
    pub fn with<P>(iter: P, func: F) -> Self
    where
        P: IntoIterator<Item = Type<T>, IntoIter = I>,
    {
        Product {
            iter: iter.into_iter(),
            func,
        }
    }
    pub fn compute(self) -> R
    where
        R: One + std::ops::Div<Output = R>,
    {
        let func = &self.func;

        // Method #1
        //  Single iteration, No allocation: Invert every flipped variant by dividing by 1
        //  i.e n(1),n(2),f(3),f(4)
        //     = (1*2)*(1/3)*(1/4)
        //  Drawback: in the case of a non-float int, 1/x = 0, invalidating the op
        //  e.g: u8:  (1*2*3*4*5)*(1/11)*(1/12)*(1/13)*(1/14)*(1/15) = 0
        //  e.g: f64: (1*2*3*4*5)*(1/11)*(1/12)*(1/13)*(1/14)*(1/15) = 0.000333000333000333
        //
        // self.iter
        //     .map(|val| match val {
        //         Type::Normal(val) => func(val),
        //         Type::Flipped(val) => R::one() / func(val),
        //     })
        //     .product()

        // Method #2 (fixes method #1)
        //  Single iteration, No allocation: Use an option to keep track of item availability
        //  Never divide by one if there's an available preceeding value
        //  i.e n(1),n(2),f(3),f(4)
        //     = (1*2)/3/4
        //  Drawback: in some cases, like in floating-point division, precision can change
        //  based on the order of digits involved
        //  e.g: u8:  (1*2*3*4*5)/11/12/13/14/15 = 0
        //  e.g: f64: (1*2*3*4*5)/11/12/13/14/15 = 0.00033300033300033295
        //
        // self.iter
        //     .fold(None, |acc, val| {
        //         Some(match val {
        //             Type::Normal(val) => match acc {
        //                 Some(acc) => acc * func(val),
        //                 None => func(val),
        //             },
        //             Type::Flipped(val) => match acc {
        //                 Some(acc) => acc / func(val),
        //                 None => R::one() / func(val),
        //             },
        //         })
        //     })
        //     .unwrap_or_else(|| R::one())

        // Method #3 (fixes method #2)
        //  Triple iteration, Two allocations: Localize operations on normal and flipped variants
        //  Use an option to keep track of item availability on each collection
        //  Converge finally, after folding each collection on its own kind
        //  Never divide arbitrarily if there's a valid non-zero, non-one value
        //  i.e n(1),n(2),f(3),f(4)
        //     = (1*2)/(3*4)
        //  Drawback: double allocations needed to keep track of normal and flipped variants
        //  e.g: u8:  (1*2*3*4*5)/(11*12*13*14*15) = 0
        //  e.g: f64: (1*2*3*4*5)/(11*12*13*14*15) = 0.000333000333000333

        let (normal, flipped): (Vec<Type<T>>, Vec<Type<T>>) =
            self.iter.partition(|val| !val.is_flipped());
        let mut proc = vec![normal, flipped].into_iter().map(|collection| {
            collection
                .into_iter()
                .map(|val| val.unwrap())
                .fold(None, |acc, val| {
                    Some(match acc {
                        Some(acc) => acc * func(val),
                        None => func(val),
                    })
                })
                .unwrap_or_else(|| R::one())
        });
        let normal = proc.next().unwrap();
        let flipped = proc.next().unwrap();
        normal / flipped
    }
}

impl<B, C, T, F> std::ops::Div<Product<C, F>> for Product<B, F>
where
    B: Iterator<Item = Type<T>>,
    C: Iterator<Item = Type<T>>,
    T: Eq + Hash,
{
    type Output = Product<ExcludedIterator<B, C, Type<T>>, F>;
    fn div(self, rhs: Product<C, F>) -> Self::Output {
        Product {
            iter: self
                .iter
                .exclude(rhs.iter)
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

impl<B, C, T, F> std::ops::Mul<Product<C, F>> for Product<B, F>
where
    B: Iterator<Item = Type<T>>,
    C: Iterator<Item = Type<T>>,
    T: Eq + Hash,
{
    type Output = Product<ExcludedIterator<B, FlippedIteratorOfTypes<C, T>, Type<T>>, F>;
    fn mul(self, rhs: Product<C, F>) -> Self::Output {
        Product {
            iter: self
                .iter
                .exclude(rhs.iter.flip())
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

impl<I: Iterator, F> IntoIterator for Product<I, F> {
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
    fn iter_type_flip() {
        // flip an iterator of types
        assert_eq!(
            vec![
                Type::Normal(5),
                Type::Flipped(10),
                Type::Flipped(15),
                Type::Normal(20)
            ]
            .into_iter()
            .flip()
            .collect::<Vec<_>>(),
            vec![
                Type::Flipped(5),
                Type::Normal(10),
                Type::Normal(15),
                Type::Flipped(20)
            ]
        );
    }
    #[test]
    fn basic_compute() {
        // (10!)
        //  = 3628800

        let val = Product::from_normal(1..=10u8, |x| x as u32);
        assert_eq!(val.compute(), 3628800);
    }
    #[test]
    fn custom_compute_mul() {
        // (4 / 2) * (2 / 4)
        //  = 1

        let func = |x| x;
        let part1 = Product::with(vec![Type::Normal(4), Type::Flipped(2)], func);
        let part2 = Product::with(vec![Type::Normal(2), Type::Flipped(4)], func);
        let result = (part1 * part2).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 1);
    }
    #[test]
    fn custom_compute_div() {
        // (4 / 2) / (2 / 4)
        //  = (4 * 4) / (2 * 2)
        //  = (16 / 4)
        //  = 4

        let func = |x| x;
        let part1 = Product::with(vec![Type::Normal(4), Type::Flipped(2)], func);
        let part2 = Product::with(vec![Type::Normal(2), Type::Flipped(4)], func);
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

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 4);
    }
    #[test]
    fn div_compute() {
        // (10!) / (3 * 4 * 5 * 6)
        //  = (1 * 2 * 7 * 8 * 9 * 10)
        //  = 10080

        let func = |x| x as u16;
        let val1 = Product::from_normal(1..=10u8, func);
        let val2 = Product::from_normal(3..=6u8, func);
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

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 10080);
    }
    #[test]
    fn div_overflow_compute() {
        // (3 * 4 * 5 * 6) / (10!)
        //  = 1 / (1 * 2 * 7 * 8 * 9 * 10)
        //  = 0.00000992063492063492

        let func = |x| x as f64;
        let val1 = Product::from_normal(1..=10u8, func);
        let val2 = Product::from_normal(3..=6u8, func);
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

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 0.0000992063492063492);
    }
    #[test]
    fn div_mixed_compute() {
        // (1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10) / (6 * 7 * 8 * 9 * 10 * 11 * 12 * 13 * 14 * 15)
        //  = (1 * 2 * 3 * 4 * 5) / (11 * 12 * 13 * 14 * 15)
        //  = 0.000333000333000333

        let func = |x| x as f64;
        let val1 = Product::from_normal(1..=10, func);
        let val2 = Product::from_normal(6..=15, func);
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

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 0.000333000333000333);
    }
    #[test]
    fn div_arbitrarily_compute() {
        // c = a * b = (1 * 2 * 3 * 4 * 5) / ((1/1) * (1/2) * (1/3) * (1/4) * (1/5))
        // c =         (1 * 2 * 3 * 4 * 5 * 1 * 2 * 3 * 4 * 5)
        // d =         (1 * 2 * 3 * 4 * 5 * 1 * 2 * 3 * 4 * 5)
        // r = c / d = (1 * 2 * 3 * 4 * 5 * 1 * 2 * 3 * 4 * 5)
        //          : /(1 * 2 * 3 * 4 * 5 * 1 * 2 * 3 * 4 * 5)
        // r =         1

        let func = |x| x;
        let a = Product::with(TypedIter::Normal(1..=5), func);
        let b = Product::with(TypedIter::Flipped(1..=5), func);
        let c = a / b;
        let d = Product::from_normal((1..=5).chain(1..=5), func);
        let result = (c / d).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 1);
    }
    #[test]
    fn mul_compute() {
        // (1 * 2 * 3 * 4 * 5) * (6 * 7 * 8 * 9 * 10)
        //  = 1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10
        //  = 3628800

        let func = |x| x;
        let val1 = Product::from_normal(1..=5, func);
        let val2 = Product::from_normal(6..=10, func);
        let mut result = (val1 * val2).into_iter().collect::<Vec<_>>();

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

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 3628800);
    }
    #[test]
    fn mul_overflow_compute() {
        // (3 * 4 * 5 * 6) * ((1/3) * (1/4) * (1/5) * (1/6) * (1/7))
        //  = (3 * 4 * 5 * 6) / (3 * 4 * 5 * 6 * 7)
        //  = 1 / 7
        //  = 0.14285714285714285

        let func = |x| x as f64;
        let val1 = Product::from_normal(3..=6, func);
        let val2 = Product::from_flipped(3..=7, func);
        let result = (val1 * val2).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![Type::Flipped(7)]);

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 0.14285714285714285);
    }
    #[test]
    fn mul_mixed_compute() {
        // (6 * 7 * 8 * 9 * 10) * ((1/3) * (1/4) * (1/5) * (1/6) * (1/7))
        //  = (6 * 7 * 8 * 9 * 10) / (3 * 4 * 5 * 6 * 7)
        //  = (8 * 9 * 10) / (3 * 4 * 5)
        //  = 12

        let func = |x| x;
        let val1 = Product::from_normal(6..=10, func);
        let val2 = Product::from_flipped(3..=7, func);
        let mut result = (val1 * val2).into_iter().collect::<Vec<_>>();

        result.sort();

        assert_eq!(
            result,
            vec![
                Type::Normal(8),
                Type::Normal(9),
                Type::Normal(10),
                Type::Flipped(3),
                Type::Flipped(4),
                Type::Flipped(5),
            ]
        );

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 12);
    }
    #[test]
    fn mul_arbitrarily_compute() {
        // c = a * b = (1 * 2 * 3 * 4 * 5) * ((1/6) * (1/7) * (1/8) * (1/9) * (1/10))
        // c =         (1 * 2 * 3 * 4 * 5) / (6 * 7 * 8 * 9 * 10)
        // d =         (6 * 7 * 8 * 9 * 10) * ((1/1) * (1/2) * (1/3) * (1/4) * (1/5))
        // d =         (6 * 7 * 8 * 9 * 10) / (1 * 2 * 3 * 4 * 5)
        // r = c * d = ((1 * 2 * 3 * 4 * 5) / (6 * 7 * 8 * 9 * 10))
        //          : *((6 * 7 * 8 * 9 * 10) / (1 * 2 * 3 * 4 * 5))
        // r =         1

        let func = |x| x;
        let a = Product::with(TypedIter::Normal(1..=5), func);
        let b = Product::with(TypedIter::Flipped(6..=10), func);
        let c = a * b;
        let d = Product::with(
            TypedIter::Normal(6..=10).chain(TypedIter::Flipped(1..=5)),
            func,
        );
        let result = (c * d).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 1);
    }
}
