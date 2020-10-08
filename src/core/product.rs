use super::{
    super::{
        exclude::{ExcludedIterator, ExcludedIteratorExt},
        One,
    },
    core::*,
};
use std::hash::Hash;

#[derive(Clone)]
pub struct Product<I: Iterator, F> {
    iter: I,
    func: F,
}

pub type ProductIntoIter<I> = DeBoxify<I>;

/// allows creating a Product value from an iterator of primitives
impl<'a, I, T: 'a, F, R> Product<TypedWithIter<TypedIter<I>>, F>
where
    I: Iterator<Item = T>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
{
    pub fn from_normal(iter: I, func: F) -> Self {
        Product::with(TypedIter::Normal(iter), func)
    }
    pub fn from_inverse(iter: I, func: F) -> Self {
        Product::with(TypedIter::Inverse(iter), func)
    }
}

impl<I, T, F, R> Product<TypedWithIter<I>, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
{
    pub fn with<P>(iter: P, func: F) -> Self
    where
        P: IntoIterator<Item = I::Item, IntoIter = I>,
    {
        Product {
            iter: TypedWithIter::new(iter.into_iter()),
            func,
        }
    }
}

impl<I, X, F> Product<I, F>
where
    I: Iterator<Item = Type<Box<dyn Resolve<Result = X>>>>,
{
    pub fn dump(self) -> I {
        self.iter
    }
}

impl<I, T, F, R> Product<I, F>
where
    I: Iterator<Item = Type<Box<T>>>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
    R: One + std::ops::Div<Output = R>,
{
    pub fn compute(self) -> R {
        let func = &self.func;

        // Method #1
        //  Single iteration, No allocation: Invert every inverse variant by dividing by 1
        //  i.e n(1),n(2),f(3),f(4)
        //     = (1*2)*(1/3)*(1/4)
        //  Drawback: in the case of a non-float int, 1/x = 0, invalidating the op
        //  e.g: u8:  (1*2*3*4*5)*(1/11)*(1/12)*(1/13)*(1/14)*(1/15) = 0
        //  e.g: f64: (1*2*3*4*5)*(1/11)*(1/12)*(1/13)*(1/14)*(1/15) = 0.000333000333000333
        //
        // self.iter
        //     .map(|val| match val {
        //         Type::Normal(val) => func(val),
        //         Type::Inverse(val) => R::one() / func(val),
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
        //             Type::Inverse(val) => match acc {
        //                 Some(acc) => acc / func(val),
        //                 None => R::one() / func(val),
        //             },
        //         })
        //     })
        //     .unwrap_or_else(|| R::one())

        // Method #3 (fixes method #2)
        //  Triple iteration, Two allocations: Localize operations on normal and inverse variants
        //  Use an option to keep track of item availability on each collection
        //  Converge finally, after folding each collection on its own kind
        //  Never divide arbitrarily if there's a valid non-zero, non-one value
        //  i.e n(1),n(2),f(3),f(4)
        //     = (1*2)/(3*4)
        //  Drawback: double allocations needed to keep track of normal and inverse variants
        //  e.g: u8:  (1*2*3*4*5)/(11*12*13*14*15) = 0
        //  e.g: f64: (1*2*3*4*5)/(11*12*13*14*15) = 0.000333000333000333
        //
        // let (normal, inverse): (Vec<Type<T>>, Vec<Type<T>>) =
        //     self.iter.partition(|val| !val.is_inverted());
        // let mut proc = vec![normal, inverse].into_iter().map(|collection| {
        //     collection
        //         .into_iter()
        //         .map(|val| val.unwrap())
        //         .fold(None, |acc, val| {
        //             Some(match acc {
        //                 Some(acc) => acc * func(val),
        //                 None => func(val),
        //             })
        //         })
        //         .unwrap_or_else(|| R::one())
        // });
        // let normal = proc.next().unwrap();
        // let inverse = proc.next().unwrap();
        // normal / inverse

        // Method #4 (fixes method #3)
        //  Single iteration, No allocation: Using a single pass over the inner iterator
        //  logically identify which branch a computation falls under save computed result
        //  within that branch. Eliminating the need for two allocations and extra iterations
        //  i.e n(1),n(2),f(3),f(4)
        //     = (1*2)/(3*4)
        //  Drawback: None
        //  e.g: u8:  (1*2*3*4*5)/(11*12*13*14*15) = 0
        //  e.g: f64: (1*2*3*4*5)/(11*12*13*14*15) = 0.000333000333000333

        let (normal, inverse) = self.iter.fold((None, None), |(normal, inverse), val| {
            let is_inverted = val.is_inverted();
            let (this, other) = if !is_inverted {
                (normal, inverse)
            } else {
                (inverse, normal)
            };
            let this = Some(match this {
                Some(prev) => prev * func(val.unwrap().resolve()),
                None => func(val.unwrap().resolve()),
            });
            if !is_inverted {
                (this, other)
            } else {
                (other, this)
            }
        });
        let normal = normal.unwrap_or_else(|| R::one());
        let inverse = inverse.unwrap_or_else(|| R::one());

        normal / inverse
    }
}

impl<I, T, F, R> Resolve for Product<I, F>
where
    I: Iterator<Item = Type<Box<T>>>,
    F: Fn(<T as Resolve>::Result) -> R,
    T: Resolve,
    R: One + std::ops::Div<Output = R>,
{
    type Result = R;
    fn resolve(self: Box<Self>) -> Self::Result {
        self.compute()
    }
}

// converts a Product struct into an iterator of Type<T>
impl<I: Iterator<Item = Type<Box<T>>>, T, F> IntoIterator for Product<I, F> {
    type Item = Type<T>;
    type IntoIter = ProductIntoIter<I>;
    fn into_iter(self) -> Self::IntoIter {
        ProductIntoIter::new(self.iter)
    }
}

impl<B, C, T, F> std::ops::Div<Product<C, F>> for Product<B, F>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator<Item = Type<Box<T>>>,
    T: Eq + Hash,
    Box<T>: Clone,
{
    type Output = Product<ExcludedIterator<B, C, Type<Box<T>>>, F>;
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
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator<Item = Type<Box<T>>>,
    T: Eq + Hash,
    Box<T>: Clone,
{
    type Output = Product<ExcludedIterator<B, FlippedIteratorOfTypes<C>, Type<Box<T>>>, F>;
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

impl<B, C, T, X, R, F1, F2> std::ops::Div<super::Sigma<C, F1>> for Product<B, F2>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator,
    T: Resolve<Result = X>,
    super::Sigma<C, F1>: Resolve<Result = X>,
    F2: Fn(X) -> R,
    T: 'static,
    C: 'static,
    F1: 'static,
{
    type Output = Product<std::vec::IntoIter<Type<Box<dyn Resolve<Result = X>>>>, F2>;
    fn div(self, rhs: super::Sigma<C, F1>) -> Self::Output {
        let mut vec: Vec<Type<Box<dyn Resolve<Result = X>>>> = vec![];
        self.iter
            .for_each(|item| vec.push(item.map(|val| val as Box<dyn Resolve<Result = X>>)));
        vec.push(Type::Inverse(Box::new(rhs) as Box<dyn Resolve<Result = X>>));

        Product {
            iter: vec.into_iter(),
            func: self.func,
        }
    }
}

impl<B, C, T, X, R, F1, F2> std::ops::Mul<super::Sigma<C, F1>> for Product<B, F2>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator,
    T: Resolve<Result = X>,
    super::Sigma<C, F1>: Resolve<Result = X>,
    F2: Fn(X) -> R,
    T: 'static,
    C: 'static,
    F1: 'static,
{
    type Output = Product<std::vec::IntoIter<Type<Box<dyn Resolve<Result = X>>>>, F2>;
    fn mul(self, rhs: super::Sigma<C, F1>) -> Self::Output {
        let mut vec: Vec<Type<Box<dyn Resolve<Result = X>>>> = vec![];
        self.iter
            .for_each(|item| vec.push(item.map(|val| val as Box<dyn Resolve<Result = X>>)));
        vec.push(Type::Normal(Box::new(rhs) as Box<dyn Resolve<Result = X>>));

        Product {
            iter: vec.into_iter(),
            func: self.func,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let part1 = Product::with(vec![Type::Normal(4), Type::Inverse(2)], func);
        let part2 = Product::with(vec![Type::Normal(2), Type::Inverse(4)], func);
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
        let part1 = Product::with(vec![Type::Normal(4), Type::Inverse(2)], func);
        let part2 = Product::with(vec![Type::Normal(2), Type::Inverse(4)], func);
        let mut result = (part1 / part2).into_iter().collect::<Vec<_>>();

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
                Type::Inverse(1),
                Type::Inverse(2),
                Type::Inverse(7),
                Type::Inverse(8),
                Type::Inverse(9),
                Type::Inverse(10)
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
                Type::Inverse(11),
                Type::Inverse(12),
                Type::Inverse(13),
                Type::Inverse(14),
                Type::Inverse(15)
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
        let b = Product::with(TypedIter::Inverse(1..=5), func);
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
        let val2 = Product::from_inverse(3..=7, func);
        let result = (val1 * val2).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![Type::Inverse(7)]);

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
        let val2 = Product::from_inverse(3..=7, func);
        let mut result = (val1 * val2).into_iter().collect::<Vec<_>>();

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
        let b = Product::with(TypedIter::Inverse(6..=10), func);
        let c = a * b;
        let d = Product::with(
            TypedIter::Normal(6..=10).chain(TypedIter::Inverse(1..=5)),
            func,
        );
        let result = (c * d).into_iter().collect::<Vec<_>>();

        assert_eq!(result, vec![]);

        let result = Product::with(result, func);
        assert_eq!(result.compute(), 1);
    }
}
