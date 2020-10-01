use std::{
    collections::{hash_map::IntoIter, HashMap},
    hash::Hash,
};

pub struct OverflowedIterator<I, T> {
    inner: I,
    cursor: Option<(T, usize)>,
}

impl<I: Iterator, T> OverflowedIterator<I, T> {
    pub fn new<F>(map: F) -> Self
    where
        F: IntoIterator<Item = (T, usize), IntoIter = I>,
        I: Iterator<Item = (T, usize)>,
    {
        OverflowedIterator {
            inner: map.into_iter(),
            cursor: None,
        }
    }
}

impl<I: Iterator, T> Iterator for OverflowedIterator<I, T>
where
    T: Copy + Eq,
    I: Iterator<Item = (T, usize)>,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some((key, ref mut val)) = self.cursor {
                *val -= 1;
                if *val == 0 {
                    self.cursor = self.inner.next();
                }
                return Some(key);
            }
            self.cursor = Some(self.inner.next()?);
        }
    }
}

pub enum OverflowStatus<T, R> {
    Excluded,
    Included(
        fn(T) -> R,
        Option<OverflowedIterator<IntoIter<T, usize>, T>>,
    ),
}

pub struct ExcludedIterator<B, C: Iterator, R> {
    base: B,
    ctrl: Option<HashMap<C::Item, usize>>,
    transformer: fn(C::Item) -> R,
    overflow: OverflowStatus<C::Item, R>,
}

impl<B, C: Iterator, R> ExcludedIterator<B, C, R> {
    pub fn new(base: B, ctrl: C) -> Self
    where
        C: Iterator<Item = R>,
        C::Item: Eq + Hash,
    {
        let mut _ctrl = HashMap::new();
        ctrl.for_each(|item| *_ctrl.entry(item).or_default() += 1);
        ExcludedIterator {
            base,
            ctrl: Some(_ctrl),
            transformer: |x| x,
            overflow: OverflowStatus::Excluded,
        }
    }
    pub fn with_transformer<V>(self, transform: fn(C::Item) -> V) -> ExcludedIterator<B, C, V> {
        ExcludedIterator {
            base: self.base,
            ctrl: self.ctrl,
            transformer: transform,
            overflow: OverflowStatus::Excluded,
        }
    }
    pub fn include_overflow(self) -> ExcludedIterator<B, C, R>
    where
        C: Iterator<Item = R>,
    {
        ExcludedIterator {
            overflow: OverflowStatus::Included(|x| x, None),
            ..self
        }
    }
    pub fn include_overflow_with(
        self,
        overflow_handler: fn(C::Item) -> R,
    ) -> ExcludedIterator<B, C, R> {
        ExcludedIterator {
            overflow: OverflowStatus::Included(overflow_handler, None),
            ..self
        }
    }
}

impl<B, C, T, R> Iterator for ExcludedIterator<B, C, R>
where
    B: Iterator<Item = T>,
    C: Iterator<Item = T>,
    T: Copy + Eq + Hash,
{
    type Item = R;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.base.next() {
                Some(val) => {
                    if self.ctrl.as_ref()?.is_empty() {
                        return Some((self.transformer)(val));
                    } else {
                        match self.ctrl.as_mut()?.get_mut(&val) {
                            Some(count) => {
                                *count -= 1;
                                if *count == 0 {
                                    self.ctrl.as_mut()?.remove(&val);
                                }
                            }
                            None => return Some((self.transformer)(val)),
                        }
                    }
                }
                None => match self.overflow {
                    OverflowStatus::Excluded => return None,
                    OverflowStatus::Included(ref handle, ref mut map) => match map {
                        None => {
                            *map = Some(OverflowedIterator::new(self.ctrl.take()?));
                        }
                        Some(iter) => return Some(handle(iter.next()?)),
                    },
                },
            };
        }
    }
}

pub trait ExcludedIteratorExt
where
    Self: Sized,
{
    type Item: Sized;
    fn exclude<Rhs: Iterator<Item = Self::Item>>(
        self,
        rhs: Rhs,
    ) -> ExcludedIterator<Self, Rhs, Self::Item>
    where
        Self::Item: Eq + Hash,
    {
        ExcludedIterator::new(self, rhs)
    }
}

impl<I> ExcludedIteratorExt for I
where
    I: Iterator,
{
    type Item = <I as Iterator>::Item;
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn basic_exclusion() {
        let exc = ExcludedIterator::new(1..=10, 3..6);
        assert_eq!(exc.collect::<Vec<_>>(), vec![1, 2, 6, 7, 8, 9, 10]);
    }
    #[test]
    fn exclusion_by_iterator_extension() {
        assert_eq!(
            (1..=10).exclude(3..6).collect::<Vec<_>>(),
            vec![1, 2, 6, 7, 8, 9, 10]
        );
        assert_eq!(
            (1..=10).exclude(3..6).exclude(7..10).collect::<Vec<_>>(),
            vec![1, 2, 6, 10]
        );
    }
    #[test]
    fn test_counted_iter() {
        use std::collections::HashMap;
        let list: HashMap<&str, usize> = [("a", 1), ("b", 2), ("c", 3)].iter().copied().collect();
        let mut items = OverflowedIterator::new(list).collect::<Vec<_>>();
        items.sort();
        assert_eq!(items, vec!["a", "b", "b", "c", "c", "c"]);
    }
    #[test]
    fn exclusion_overflow() {
        let mut exc = ((3..6).chain(11..=15)).exclude(1..=10);
        let included = exc.by_ref().collect::<Vec<_>>();
        let mut overflow = exc.include_overflow().collect::<Vec<_>>();
        overflow.sort();
        assert_eq!(included, vec![11, 12, 13, 14, 15]);
        assert_eq!(overflow, vec![1, 2, 6, 7, 8, 9, 10]);
    }
    #[test]
    fn exclusion_transform() {
        assert_eq!(
            (1..=10)
                .exclude(4..=8u8)
                .with_transformer(|val| val as f32)
                .collect::<Vec<_>>(),
            vec![1.0, 2.0, 3.0, 9.0, 10.0]
        );
    }
    #[test]
    fn exclusion_with_overflow() {
        let mut list = ((3..=6).chain(11..=15))
            .exclude(1..=10)
            .include_overflow()
            .collect::<Vec<_>>();
        list.sort();
        assert_eq!(list, [1, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
    }
    #[test]
    fn exclusion_with_overflow_with() {
        let mut list = ((3..=6).chain(11..=15u8))
            .exclude(1..=10)
            .include_overflow_with(|val| val.pow(2))
            .collect::<Vec<_>>();
        list.sort();
        assert_eq!(list, vec![1, 4, 11, 12, 13, 14, 15, 49, 64, 81, 100]);
    }
    #[test]
    fn exclusion_transform_with_overflow() {
        // (3 * 4 * 5 * 6) / 10!
        //   = 1 / (1 * 2 * 7 * 8 * 9 * 10)
        assert_eq!(
            (3..=6)
                .exclude(1..=10u8)
                .with_transformer(|val| val as f32)
                .include_overflow_with(|val| 1.0 / val as f32)
                .product::<f32>(),
            0.00009920636
        );
    }
}
