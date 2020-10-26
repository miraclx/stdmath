use std::{
    collections::{hash_map::DefaultHasher, BTreeMap, HashMap},
    hash::{Hash, Hasher},
};

fn hash<T: Hash>(val: &T) -> u64 {
    let mut state = DefaultHasher::new();
    val.hash(&mut state);
    state.finish()
}

#[derive(Clone)]
pub enum OverflowState<T, R> {
    Excluded,
    Included(fn(T) -> R),
}

#[cfg(feature = "order")]
#[derive(Clone)]
struct DictionaryEntry<T> {
    cursor: usize,
    slots: Vec<(usize, T)>,
}

#[derive(Clone)]
pub struct ExcludedIterator<B, C: Iterator, R> {
    base: B,
    #[cfg(feature = "order")]
    ctrl: HashMap<u64, DictionaryEntry<C::Item>>,
    #[cfg(not(feature = "order"))]
    ctrl: HashMap<u64, Vec<C::Item>>,
    #[cfg(feature = "order")]
    hash_entries: BTreeMap<usize, u64>,
    transformer: fn(C::Item) -> R,
    overflow: OverflowState<C::Item, R>,
}

impl<B, C: Iterator, R> ExcludedIterator<B, C, R> {
    #[cfg(not(feature = "order"))]
    pub fn new(base: B, ctrl: C) -> Self
    where
        C: Iterator<Item = R>,
        C::Item: Eq + Hash,
    {
        let mut _ctrl: HashMap<u64, Vec<C::Item>> = HashMap::new();
        ctrl.for_each(|item| _ctrl.entry(hash(&item)).or_default().push(item));
        ExcludedIterator {
            base,
            ctrl: _ctrl,
            #[inline]
            transformer: |x| x,
            overflow: OverflowState::Excluded,
        }
    }
    #[cfg(feature = "order")]
    pub fn new(base: B, ctrl: C) -> Self
    where
        C: Iterator<Item = R>,
        C::Item: Eq + Hash,
    {
        let mut _ctrl: HashMap<u64, DictionaryEntry<C::Item>> = HashMap::new();
        let hash_entries = ctrl
            .enumerate()
            .map(|(index, item)| {
                let hash = hash(&item);

                _ctrl
                    .entry(hash)
                    .or_insert_with(|| DictionaryEntry {
                        cursor: 0,
                        slots: vec![],
                    })
                    .slots
                    .push((index, item));

                (index, hash)
            })
            .collect();
        ExcludedIterator {
            base,
            ctrl: _ctrl,
            hash_entries,
            #[inline]
            transformer: |x| x,
            overflow: OverflowState::Excluded,
        }
    }
    pub fn with_transformer<V>(self, transform: fn(C::Item) -> V) -> ExcludedIterator<B, C, V> {
        ExcludedIterator {
            base: self.base,
            ctrl: self.ctrl,
            #[cfg(feature = "order")]
            hash_entries: self.hash_entries,
            #[inline]
            transformer: transform,
            overflow: OverflowState::Excluded,
        }
    }
    pub fn include_overflow(self) -> ExcludedIterator<B, C, R>
    where
        C: Iterator<Item = R>,
    {
        ExcludedIterator {
            overflow: OverflowState::Included(
                #[inline]
                |x| x,
            ),
            ..self
        }
    }
    pub fn include_overflow_with(
        self,
        overflow_handler: fn(C::Item) -> R,
    ) -> ExcludedIterator<B, C, R> {
        ExcludedIterator {
            overflow: OverflowState::Included(overflow_handler),
            ..self
        }
    }
}

impl<B, C, T, R> Iterator for ExcludedIterator<B, C, R>
where
    B: Iterator<Item = T>,
    C: Iterator<Item = T>,
    T: Eq + Hash,
{
    type Item = R;
    #[cfg(not(feature = "order"))]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.base.next() {
                Some(val) => {
                    if self.ctrl.is_empty() {
                        return Some((self.transformer)(val));
                    } else {
                        let hash = hash(&val);
                        match self.ctrl.get_mut(&hash) {
                            Some(items) => {
                                let val_ = items
                                    .last()
                                    .expect("there should be at least one item here");
                                if val != *val_ {
                                    return Some((self.transformer)(val));
                                }
                                items.pop();
                                if items.len() == 0 {
                                    self.ctrl.remove(&hash);
                                }
                            }
                            None => return Some((self.transformer)(val)),
                        }
                    }
                }
                None => match self.overflow {
                    OverflowState::Excluded => return None,
                    OverflowState::Included(handle) => {
                        let (key, value, len) =
                            self.ctrl.iter_mut().next().map(|(hash, items)| {
                                (
                                    *hash,
                                    items.pop().expect("there should be at least one item here"),
                                    items.len(),
                                )
                            })?;
                        if len == 0 {
                            self.ctrl.remove(&key);
                        }
                        return Some(handle(value));
                    }
                },
            };
        }
    }
    #[cfg(feature = "order")]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.base.next() {
                Some(val) => {
                    if self.ctrl.is_empty() {
                        return Some((self.transformer)(val));
                    } else {
                        let hash = hash(&val);
                        match self.ctrl.get_mut(&hash) {
                            Some(entry) => {
                                let (index, val_) = entry
                                    .slots
                                    .get(entry.cursor)
                                    .expect("entry slot cursor out of bounds");
                                if val != *val_ {
                                    return Some((self.transformer)(val));
                                }
                                self.hash_entries.remove(index);
                                entry.cursor += 1;
                                if entry.cursor == entry.slots.len() {
                                    self.ctrl.remove(&hash);
                                }
                            }
                            None => return Some((self.transformer)(val)),
                        }
                    }
                }
                None => match self.overflow {
                    OverflowState::Excluded => return None,
                    OverflowState::Included(handle) => {
                        let index = *self.hash_entries.keys().next()?;
                        let hash = self.hash_entries.remove(&index)?;
                        let DictionaryEntry { slots, cursor } = self
                            .ctrl
                            .get_mut(&hash)
                            .expect("can't find hash entry within dictionary");
                        let (_, val) = slots.pop()?;
                        if *cursor == slots.len() {
                            self.ctrl.remove(&hash);
                        }
                        return Some(handle(val));
                    }
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
    fn exclusion_overflow() {
        let mut exc = ((3..6).chain(11..=15)).exclude(1..=10);
        let included = exc.by_ref().collect::<Vec<_>>();
        let mut overflow = exc.include_overflow().collect::<Vec<_>>();
        overflow.sort(); // not necessary if feature="order"
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
        list.sort(); // not necessary if feature="order"
        assert_eq!(list, [1, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
    }
    #[test]
    fn exclusion_with_overflow_with() {
        let mut list = ((3..=6).chain(11..=15u8))
            .exclude(1..=10)
            .include_overflow_with(|val| val.pow(2))
            .collect::<Vec<_>>();
        list.sort(); // not necessary if feature="order"
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
