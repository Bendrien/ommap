use std::iter::Zip;
use std::slice;
use std::vec;
use std::ops::Range;

#[derive(Debug)]
pub struct Ommap<K, V> {
    keys: Vec<K>,
    values: Vec<V>,
}

impl<K: Ord, V> Ommap<K, V> {
    /// Constructs a new, empty `Ommap<K,V>`.
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

    /// Get the first index associated with the given key next to the given index (inclusive).
    #[inline]
    fn start_index(&self, key: &K, index: usize) -> usize {
        index -
            self.keys[..index].iter()
                .rev()
                .position(|k| *k != *key)
                .unwrap_or(0)
    }

    /// Get the last index associated with the given key next to the given index (exclusive).
    #[inline]
    fn end_index(&self, key: &K, index: usize) -> usize {
        index +
            self.keys[index..].iter()
                .position(|k| *k != *key)
                .unwrap_or(1)
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

    /// Get the range including all given keys.
    ///
    /// Assumes the given keys are in sorted order.
    /// Returns `None` if there is no entry for any given key.
    #[allow(dead_code)]
    fn range_multi(&self, keys: &[&K]) -> Option<Range<usize>> {
        if keys.is_empty() || self.keys.is_empty() { return None; }

        if *self.keys.last().unwrap() < **keys.last().unwrap() { return None; }

        if let Some(start) = keys.iter()
            .map(|&key| (key, self.keys.binary_search(key)))
            .find(|&(_,search_result)| search_result.is_ok())
            .map(|(key,search_result)| self.start_index(key, search_result.ok().unwrap()))
        {
            if let Some(end) = keys.iter()
                .rev()
                .map(|&key| (key, self.keys.binary_search(key)))
                .find(|&(_,search_result)| search_result.is_ok())
                .map(|(key,search_result)| self.end_index(key, search_result.ok().unwrap()))
            {
                return Some(Range { start: start, end: end })
            }
        }
        None
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Swaps two elements in a slice.
    pub fn swap(&mut self, a: usize, b: usize) {
        self.keys.swap(a, b);
        self.values.swap(a, b);
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    pub fn truncate(&mut self, len: usize) {
        self.keys.truncate(len);
        self.values.truncate(len);
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

    /// Removes all elements associated with the given key preserving sorted order.
    ///
    /// Returns all removed elements if there where some otherwise `None`.
    pub fn remove(&mut self, key: &K) -> Option<Vec<V>> {
        if let Some(range) = self.range(key) {
            self.keys.drain(range.clone());
            return Some(self.values.drain(range).collect());
        }
        None
    }

    /// Removes all elements associated with the given keys preserving sorted order.
    ///
    /// Assumes the given keys are in sorted order.
    pub fn remove_multi(&mut self, keys: &[K]) {
        if keys.is_empty() || self.keys.is_empty() { return; }
        if *self.keys.last().unwrap() < *keys.last().unwrap() { return; }
        if let Some(start) = keys.iter()
            .map(|key| (key, self.keys.binary_search(&key)))
            .find(|&(_,search_result)| search_result.is_ok())
            .map(|(key,search_result)| self.start_index(&key, search_result.ok().unwrap()))
        {
            let len = self.len();
            let mut del = 0;
            {
                let mut iter = keys.iter().peekable();

                for i in start..len {
                    while let Some(&k) = iter.peek() {
                        if *k < self.keys[i] {
                            iter.next();
                        } else {
                            break;
                        }
                    }

                    if iter.peek().is_some() && **iter.peek().unwrap() == self.keys[i] {
                        del += 1;
                    } else if del > 0 {
                        self.swap(i - del, i);
                    }
                }
            }
            if del > 0 {
                self.truncate(len - del);
            }
        }
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
}

/////////////////////////////////////////
// Iterators
/////////////////////////////////////////

impl<K, V> Ommap<K, V> {
    pub fn into_iter(self) -> Zip<vec::IntoIter<K>, vec::IntoIter<V>> {
        self.keys.into_iter().zip(self.values.into_iter())
    }

    pub fn iter<'a>(&'a self) -> Zip<slice::Iter<'a, K>, slice::Iter<'a, V>> {
        self.keys.iter().zip(self.values.iter())
    }

    pub fn iter_mut<'a>(&'a mut self) -> Zip<slice::Iter<'a, K>, slice::IterMut<'a, V>> {
        self.keys.iter().zip(self.values.iter_mut())
    }

    pub fn keys<'a>(&'a self) -> slice::Iter<'a, K> {
        self.keys.iter()
    }

    pub fn values<'a>(&'a self) -> slice::Iter<'a, V> {
        self.values.iter()
    }

    pub fn values_mut<'a>(&'a mut self) -> slice::IterMut<'a, V> {
        self.values.iter_mut()
    }
}

struct FilterZip<A, B> {
    a: A,
    b: B,
}

impl<K, V, W, A, B> Iterator for FilterZip<A, B>
    where K: Ord,
          A: Iterator<Item=(K, V)>,
          B: Iterator<Item=(K, W)>,
{
    type Item = (K, (V, W));
    fn next(&mut self) -> Option<Self::Item> {
        if let (Some((mut ka, mut va)), Some((mut kb, mut vb))) = (self.a.next(), self.b.next()) {
            while ka < kb {
                if let Some((kn,vn)) = self.a.next() {
                    ka = kn;
                    va = vn;
                } else { return None; }
            }
            while ka > kb {
                if let Some((kn,vn)) = self.b.next() {
                    kb = kn;
                    vb = vn;
                } else { return None; }
            }
            return Some((ka, (va, vb)));
        }
        None
    }
}

trait ToFilterZip<B>: Sized {
    /// Zips the iterators by matching their keys against each other in ascending order
    /// and only yielding the equal ones.
    fn filter_zip(self, B) -> FilterZip<Self, B>;
}

impl<K, V, W, A, B> ToFilterZip<B> for A
    where K: Ord,
          A: Iterator<Item=(K, V)>,
          B: Iterator<Item=(K, W)>,
{
    fn filter_zip(self, b: B) -> FilterZip<A, B> {
        FilterZip {
            a: self,
            b: b,
        }
    }
}

/////////////////////////////////////////
// Tests
/////////////////////////////////////////

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
        assert_eq!(map.get_mut(&42).is_empty(), true);

        map.insert(3, 3);
        map.insert(2, 2_1);
        map.insert(1, 1);
        map.insert(2, 2_2);
        map.insert(4, 4);
        map.insert(2, 2_3);

        {
            let mut iter = map.get_mut(&2).iter_mut();
            assert_eq!(iter.next(), Some(&mut 2_1));
            assert_eq!(iter.next(), Some(&mut 2_2));
            assert_eq!(iter.next(), Some(&mut 2_3));
            assert_eq!(iter.next(), None);
        }

        assert_eq!(map.get_mut(&42).is_empty(), true);
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
    fn remove_multi() {
        let mut map = Ommap::new();
        map.insert(3, 3);
        map.insert(4, 4_1);
        map.insert(2, 2_1);
        map.insert(5, 5);
        map.insert(4, 4_2);
        map.insert(1, 1);
        map.insert(2, 2_2);
        map.insert(2, 2_3);

        map.remove_multi(&[2,4]);

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&1, &1)));
        assert_eq!(iter.next(), Some((&3, &3)));
        assert_eq!(iter.next(), Some((&5, &5)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn remove_on_heavy_load() {
        let mut map = Ommap::new();
        let mut v = Vec::new();

        for i in 0..1_000_000 {
            v.push(i);
            map.insert(i, i);
        }
        map.remove_multi(&v[..]);

        assert_eq!(map.len(), 0);
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
        assert_eq!(iter.next(), Some((&1, &mut 'a')));
        assert_eq!(iter.next(), Some((&2, &mut 'b')));
        assert_eq!(iter.next(), Some((&3, &mut 'c')));
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
    fn filter_zip() {
        let mut a = Ommap::new();
        let mut b = Ommap::new();
        a.insert(1,1);
        a.insert(1,5);
        b.insert(1,6);
        a.insert(2,4);
        b.insert(2,7);
        a.insert(3,3);
        b.insert(3,8);
        a.insert(5,2);
        b.insert(5,9);

        let mut iter = a.iter().filter_zip(b.iter());
        assert_eq!(iter.next(), Some((&1, (&1,&6))));
        assert_eq!(iter.next(), Some((&2, (&4,&7))));
        assert_eq!(iter.next(), Some((&3, (&3,&8))));
        assert_eq!(iter.next(), Some((&5, (&2,&9))));
        assert_eq!(iter.next(), None);
    }
}