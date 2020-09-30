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
                    if self.ctrl.as_ref()?.len() == 0 {
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
