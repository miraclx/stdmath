use std::{collections::HashMap, hash::Hash};

pub struct ExcludedIterator<B, C: Iterator> {
    base: B,
    ctrl: HashMap<C::Item, usize>,
}

impl<B, C: Iterator> ExcludedIterator<B, C> {
    pub fn new(base: B, ctrl: C) -> Self
    where
        C::Item: Eq + Hash,
    {
        let mut _ctrl = HashMap::new();
        ctrl.for_each(|item| *_ctrl.entry(item).or_default() += 1);
        ExcludedIterator { base, ctrl: _ctrl }
    }
}

impl<B, C, T> Iterator for ExcludedIterator<B, C>
where
    B: Iterator<Item = T>,
    C: Iterator<Item = T>,
    T: Eq + Hash,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        'top: loop {
            let val = self.base.next()?;
            if self.ctrl.len() == 0 {
                return Some(val);
            } else {
                match self.ctrl.get_mut(&val) {
                    Some(count) => {
                        *count -= 1;
                        if *count == 0 {
                            self.ctrl.remove(&val);
                        }
                    }
                    None => break 'top Some(val),
                }
            }
        }
    }
}
pub trait ExcludedIteratorExt: Iterator
where
    Self: Sized,
{
    fn exclude<Rhs: Iterator<Item = Self::Item>>(self, rhs: Rhs) -> ExcludedIterator<Self, Rhs>
    where
        Self::Item: Eq + Hash,
    {
        ExcludedIterator::new(self, rhs)
    }
}

impl<I> ExcludedIteratorExt for I where I: Iterator {}
