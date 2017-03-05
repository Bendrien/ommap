use std::iter::Zip;
use std::slice;
use std::vec;
use std::ops::Range;


#[derive(Debug)]
pub struct Ommap<K, V> {
    keys: Vec<K>,
    values: Vec<V>,
}

impl<K, V> Ommap<K, V>
    where K: Ord
{
    /// Constructs a new, empty `Ommap<k,V>`.
    pub fn new() -> Self {
        Ommap {
            keys: Vec::new(),
            values: Vec::new(),
        }
    }

    /// Get the index of a given key.
    ///
    /// Returns `None` if there is no entry for the key.
    #[inline]
    fn index(&self, key: &K) -> Option<usize> {
        if self.keys.is_empty() || *self.keys.last().unwrap() < *key {
            return None;
        }
        self.keys.binary_search(key).ok()
    }

    /// Get the first index associated with the given key next to the given index (inclusie).
    #[inline]
    fn start_index(&self, key: &K, index: usize) -> usize {
        index -
            self.keys[..index].iter().rev()
                .position(|k| *k != *key).unwrap_or(0)
    }

    /// Get the last index associated with the given key next to the given index (exclusive).
    #[inline]
    fn end_index(&self, key: &K, index: usize) -> usize {
        index +
            self.keys[index..].iter()
                .position(|k| *k != *key).unwrap_or(1)
    }

    /// Get the range associated with the given key.
    ///
    /// Returns `None` if there is no entry for the key.
    #[inline]
    fn range(&self, key: &K) -> Option<Range<usize>> {
        if let Some(index) = self.index(key) {
            return Some(Range {
                start: self.start_index(key, index),
                end: self.end_index(key, index),
            });
        }
        None
    }

    /// Inserts an element into the map at the key's position maintaining sorted order.
    ///
    /// If there is already an entry for that key (or multiple) it will be inserted right after.
    pub fn insert(&mut self, key: K, value: V) {
        if self.keys.is_empty() || *self.keys.last().unwrap() <= key {
            self.keys.push(key);
            self.values.push(value);
        } else {
            let index = match self.keys.binary_search(&key) {
                Ok(index) => self.end_index(&key, index),
                Err(index) => index,
            };
            self.keys.insert(index, key);
            self.values.insert(index, value);
        }
    }

    /// Removes all elements associated with the given key.
    ///
    /// Returns all removed elements if there where some otherwise `None`.
    pub fn remove(&mut self, key: &K) -> Option<Vec<V>> {
        if let Some(range) = self.range(key) {
            self.keys.drain(range.clone());
            return Some(self.values.drain(range).collect());
        }
        None
    }

    /// Gets all elements associated with the given key as `slice`.
    ///
    /// If there isn't an entry for the given key the returned slice will be empty.
    pub fn get<'a>(&'a self, key: &K) -> &'a [V] {
        if self.values.is_empty() {
            &self.values
        } else if let Some(range) = self.range(key) {
            &self.values[range]
        } else {
            &self.values[..0]
        }
    }

    /// Gets all elements associated with the given key as mutable `slice`.
    ///
    /// If there isn't an entry for the given key the returned slice will be empty.
    pub fn get_mut<'a>(&'a mut self, key: &K) -> &'a mut [V] {
        if self.values.is_empty() {
            &mut self.values
        } else if let Some(range) = self.range(key) {
            &mut self.values[range]
        } else {
            &mut self.values[..0]
        }
    }

    pub fn into_iter(self) -> Zip<vec::IntoIter<K>, vec::IntoIter<V>> {
        self.keys.into_iter().zip(self.values.into_iter())
    }

    pub fn iter<'a>(&'a self) -> Zip<slice::Iter<'a, K>, slice::Iter<'a, V>> {
        self.keys.iter().zip(self.values.iter())
    }

    pub fn iter_mut<'a>(&'a mut self) -> Zip<slice::IterMut<'a, K>, slice::IterMut<'a, V>> {
        self.keys.iter_mut().zip(self.values.iter_mut())
    }

    pub fn keys<'a>(&'a self) -> slice::Iter<'a, K> {
        self.keys.iter()
    }

    pub fn keys_mut<'a>(&'a mut self) -> slice::IterMut<'a, K> {
        self.keys.iter_mut()
    }

    pub fn values<'a>(&'a self) -> slice::Iter<'a, V> {
        self.values.iter()
    }

    pub fn values_mut<'a>(&'a mut self) -> slice::IterMut<'a, V> {
        self.values.iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get() {
        let mut map = Ommap::new();
        assert_eq!(map.get(&42).is_empty(), true);

        map.insert(3, 3);
        map.insert(2, 2_1);
        map.insert(1, 1);
        map.insert(2, 2_2);
        map.insert(4, 4);
        map.insert(2, 2_3);

        let mut iter = map.get(&2).iter();
        assert_eq!(iter.next(), Some(&2_1));
        assert_eq!(iter.next(), Some(&2_2));
        assert_eq!(iter.next(), Some(&2_3));
        assert_eq!(iter.next(), None);

        assert_eq!(map.get(&42).is_empty(), true);
    }

    #[test]
    fn get_mut() {
        let mut map = Ommap::new();
        map.insert(3, 3);
        map.insert(2, 2_1);
        map.insert(1, 1);
        map.insert(2, 2_2);
        map.insert(4, 4);
        map.insert(2, 2_3);

        let mut iter = map.get_mut(&2).iter_mut();
        assert_eq!(iter.next(), Some(&mut 2_1));
        assert_eq!(iter.next(), Some(&mut 2_2));
        assert_eq!(iter.next(), Some(&mut 2_3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn remove() {
        let mut map = Ommap::new();
        map.insert(3, 3);
        map.insert(2, 2_1);
        map.insert(1, 1);
        map.insert(2, 2_2);
        map.insert(2, 2_3);

        let v = map.remove(&2).unwrap();
        let mut iter = v.iter();
        assert_eq!(iter.next(), Some(&21));
        assert_eq!(iter.next(), Some(&22));
        assert_eq!(iter.next(), Some(&23));
        assert_eq!(iter.next(), None);

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&1, &1)));
        assert_eq!(iter.next(), Some((&3, &3)));
        assert_eq!(iter.next(), None);
    }


    #[test]
    fn into_iter() {
        let mut map = Ommap::new();
        map.insert(3, 'c');
        map.insert(1, 'a');
        map.insert(2, 'b');

        let mut iter = map.into_iter();
        assert_eq!(iter.next(), Some((1, 'a')));
        assert_eq!(iter.next(), Some((2, 'b')));
        assert_eq!(iter.next(), Some((3, 'c')));
    }

    #[test]
    fn iter() {
        let mut map = Ommap::new();
        map.insert(3, 'c');
        map.insert(2, 'b');
        map.insert(1, 'a');

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&1, &'a')));
        assert_eq!(iter.next(), Some((&2, &'b')));
        assert_eq!(iter.next(), Some((&3, &'c')));
    }


    #[test]
    fn iter_mut() {
        let mut map = Ommap::new();
        map.insert(1, 'a');
        map.insert(3, 'c');
        map.insert(2, 'b');

        let mut iter = map.iter_mut();
        assert_eq!(iter.next(), Some((&mut 1, &mut 'a')));
        assert_eq!(iter.next(), Some((&mut 2, &mut 'b')));
        assert_eq!(iter.next(), Some((&mut 3, &mut 'c')));
    }

    #[test]
    fn values() {
        let mut map = Ommap::new();
        map.insert(3, 'c');
        map.insert(2, 'b');
        map.insert(1, 'a');

        let mut iter = map.values();
        assert_eq!(iter.next(), Some(&'a'));
        assert_eq!(iter.next(), Some(&'b'));
        assert_eq!(iter.next(), Some(&'c'));
    }


    #[test]
    fn values_mut() {
        let mut map = Ommap::new();
        map.insert(3, 'c');
        map.insert(2, 'b');
        map.insert(1, 'a');

        let mut iter = map.values_mut();
        assert_eq!(iter.next(), Some(&mut 'a'));
        assert_eq!(iter.next(), Some(&mut 'b'));
        assert_eq!(iter.next(), Some(&mut 'c'));
    }

    #[test]
    fn keys() {
        let mut map = Ommap::new();
        map.insert(3, 'c');
        map.insert(2, 'b');
        map.insert(1, 'a');

        let mut iter = map.keys();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
    }

    #[test]
    fn keys_mut() {
        let mut map = Ommap::new();
        map.insert(3, 'c');
        map.insert(2, 'b');
        map.insert(1, 'a');

        let mut iter = map.keys_mut();
        assert_eq!(iter.next(), Some(&mut 1));
        assert_eq!(iter.next(), Some(&mut 2));
        assert_eq!(iter.next(), Some(&mut 3));
    }
}