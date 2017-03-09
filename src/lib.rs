extern crate core;

mod iter;

use std::iter::Zip;
use std::slice;
use std::vec;
use std::ops::Range;
use core::ptr;

#[derive(Debug)]
pub struct Ommap<K, V> {
    keys: Vec<K>,
    values: Vec<V>,
}

impl<K: Ord, V> Ommap<K, V> {
    /// Constructs a new, empty `Ommap<K, V>`.
    pub fn new() -> Self {
        Ommap {
            keys: Vec::new(),
            values: Vec::new(),
        }
    }

    /// Converts the vec into an `Ommap<K, V>`.
    pub fn from(other: Vec<(K, V)>) -> Self {
        let unzip = other.into_iter().unzip();
        Ommap {
            keys: unzip.0,
            values: unzip.1,
        }
    }

    /// Get the index of a given key.
    ///
    /// Returns `None` if there is no entry for the key.
    #[inline]
    fn index(&self, key: &K) -> Option<usize> {
        if self.is_inner_bounds(key) {
            return self.keys.binary_search(key).ok();
        }
        None
    }

    /// Get the first index associated with the given key next to the given index (inclusive).
    #[inline]
    fn first_index(&self, key: &K, index: usize) -> usize {
        self.keys[..index].iter()
            .rev()
            .take_while(|&k| k == key)
            .fold(index, |acc, _| acc - 1 )
    }

    /// Get the last index associated with the given key next to the given index (exclusive).
    #[inline]
    fn last_index_exclusive(&self, key: &K, index: usize) -> usize {
        self.keys[index..].iter()
            .take_while(|&k| k == key)
            .fold(index, |acc, _| acc + 1 )
    }

    /// Get the range associated with the given key.
    ///
    /// Returns `None` if there is no entry for the key.
    #[inline]
    fn range(&self, key: &K) -> Option<Range<usize>> {
        if let Some(index) = self.index(key) {
            return Some(Range {
                start: self.first_index(key, index),
                end: self.last_index_exclusive(key, index),
            });
        }
        None
    }

    #[inline]
    fn is_inner_bounds(&self, key: &K) -> bool {
        if let Some(first) = self.keys.first() {
            return first <= key && key <= self.keys.last().unwrap();
        }
        false
    }

    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        self.keys.truncate(len);
        self.values.truncate(len);
    }

    /// Inserts an element into the map at the key's position maintaining sorted order.
    ///
    /// If there is already an entry for that key (or multiple) it will be inserted right after
    /// maintaining insertion order.
    pub fn push(&mut self, key: K, value: V) {
        if self.keys.is_empty() || *self.keys.last().unwrap() <= key {
            self.keys.push(key);
            self.values.push(value);
        } else {
            let index = match self.keys.binary_search(&key) {
                Ok(index) => self.last_index_exclusive(&key, index),
                Err(index) => index,
            };
            self.keys.insert(index, key);
            self.values.insert(index, value);
        }
    }

    pub fn pop(&mut self, key: &K) -> Option<V> {
        if !self.is_inner_bounds(key) {
            return None;
        }
        if self.keys.last().unwrap() == key {
            self.keys.pop();
            return self.values.pop();
        }
        let index = match self.keys.binary_search(key) {
            Ok(index) => self.last_index_exclusive(key, index) - 1,
            Err(_) => return None,
        };
        self.keys.remove(index);
        Some(self.values.remove(index))
    }

    /// Returns the first value associated with the key, or None if it doesn't exist.
    pub fn first(&self, key: &K) -> Option<&V> {
        if let Some(index) = self.index(key) {
            return Some(&self.values[self.first_index(key, index)]);
        }
        None
    }

    /// Returns the last value associated with the key, or None if it doesn't exist.
    pub fn last(&self, key: &K) -> Option<&V> {
        if let Some(index) = self.index(key) {
            return Some(&self.values[self.last_index_exclusive(key, index) - 1]);
        }
        None
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
        if keys.is_empty() || !self.is_inner_bounds(keys.first().unwrap())
            || !self.is_inner_bounds(keys.last().unwrap()) {
            return;
        }
        if let Some(start) = keys.iter()
            .map(|key| (key, self.keys.binary_search(key)))
            .find(|&(_,search_result)| search_result.is_ok())
            .map(|(key,search_result)| self.first_index(key, search_result.ok().unwrap()))
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
                        let j = i - del;
                        self.keys.swap(j, i);
                        self.values.swap(j, i);
                    }
                }
            }
            if del > 0 {
                self.truncate(len - del);
            }
        }
    }

    fn index_count<'a>(&self, elem: &[(K, V)]) -> Vec<(usize, usize)> {
        let mut vec = Vec::new();
        let mut iter = elem.iter().peekable();
        let mut cnt = 0;
        while let Some(key) = iter.next().map(|&(ref key,_)| key) {
            cnt += 1;
            if let Some(peek) = iter.peek().map(|&&(ref key,_)| key) {
                if key == peek {
                    continue;
                }
            }
            let index = match self.keys.binary_search(key) {
                Ok(index) => self.last_index_exclusive(key, index),
                Err(index) => index,
            };
            vec.push((index, cnt.clone()));
            cnt = 0;
        }
        vec
    }

    /// Inserts all elements into the map at theirs key position maintaining sorted order.
    ///
    /// If there is already an entry (or multiple) for any key the corresponding element
    /// will be inserted right after maintaining insertion order.
    pub fn insert_multi(&mut self, elem: Vec<(K, V)>) {
        let len = self.len();
        let elem_count = elem.len();
        let new_len = len + elem_count;

        self.keys.reserve_exact(elem_count);
        self.values.reserve_exact(elem_count);

        let mut index_count_iter = self.index_count(&elem).into_iter().rev();
        let mut elem_iter = elem.into_iter().rev();

        let mut remaining_all = elem_count as isize;
        let mut end_index = len;

        unsafe {
            while let Some((index, index_count)) = index_count_iter.next() {
                let key_ptr = self.keys.as_mut_ptr().offset(index as isize);
                let value_ptr = self.values.as_mut_ptr().offset(index as isize);

                if index < end_index {
                    let count = end_index - index;
                    ptr::copy(key_ptr, key_ptr.offset(remaining_all), count);
                    ptr::copy(value_ptr, value_ptr.offset(remaining_all), count);
                    end_index -= count;
                }

                for _ in 0..index_count {
                    remaining_all -= 1;
                    let (key, value) = elem_iter.next().unwrap();
                    ptr::write(key_ptr.offset(remaining_all), key);
                    ptr::write(value_ptr.offset(remaining_all), value);
                }
            }
            self.keys.set_len(new_len);
            self.values.set_len(new_len);
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


    /////////////////////////////////////
    // Iterators
    /////////////////////////////////////


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


    /////////////////////////////////////
    // Tests
    /////////////////////////////////////


#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn first_last() {
        let map = Ommap::from(vec!((1, 0), (3, 1), (3, 2), (3, 3), (5, 0)));
        assert_eq!(map.first(&1), Some(&0));
        assert_eq!(map.first(&3), Some(&1));
        assert_eq!(map.first(&5), Some(&0));
        assert_eq!(map.last(&1), Some(&0));
        assert_eq!(map.last(&3), Some(&3));
        assert_eq!(map.last(&5), Some(&0));
    }

    #[test]
    fn insert_multi() {
        let mut map = Ommap::new();
        map.insert_multi(vec!((1, 1), (2, 2), (3, 3)));

        {
            let mut iter = map.iter();
            assert_eq!(iter.next(), Some((&1, &1)));
            assert_eq!(iter.next(), Some((&2, &2)));
            assert_eq!(iter.next(), Some((&3, &3)));
            assert_eq!(iter.next(), None);
        }

        map.insert_multi(vec!((0, 0), (2, 22), (4, 4)));

        println!("{:?}", map);
        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&0, &0)));
        assert_eq!(iter.next(), Some((&1, &1)));
        assert_eq!(iter.next(), Some((&2, &2)));
        assert_eq!(iter.next(), Some((&2, &22)));
        assert_eq!(iter.next(), Some((&3, &3)));
        assert_eq!(iter.next(), Some((&4, &4)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn pop_elem() {
        let mut map = Ommap::new();
        map.push(3, 3);
        map.push(2, 2_1);
        map.push(1, 1);
        map.push(2, 2_2);

        assert_eq!(map.pop(&1), Some(1));
        assert_eq!(map.pop(&1), None);
        assert_eq!(map.pop(&3), Some(3));
        assert_eq!(map.pop(&3), None);
        assert_eq!(map.pop(&2), Some(2_2));
        assert_eq!(map.pop(&2), Some(2_1));
        assert_eq!(map.pop(&2), None);
    }

    #[test]
    fn get() {
        let mut map = Ommap::new();
        assert_eq!(map.get(&42).is_empty(), true);

        map.push(3, 3);
        map.push(2, 2_1);
        map.push(1, 1);
        map.push(2, 2_2);
        map.push(4, 4);
        map.push(2, 2_3);

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

        map.push(3, 3);
        map.push(2, 2_1);
        map.push(1, 1);
        map.push(2, 2_2);
        map.push(4, 4);
        map.push(2, 2_3);

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
        map.push(3, 3);
        map.push(2, 2_1);
        map.push(1, 1);
        map.push(2, 2_2);
        map.push(2, 2_3);

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
        map.push(3, 3);
        map.push(4, 4_1);
        map.push(2, 2_1);
        map.push(5, 5);
        map.push(4, 4_2);
        map.push(1, 1);
        map.push(2, 2_2);
        map.push(2, 2_3);

        map.remove_multi(&[2,4]);

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&1, &1)));
        assert_eq!(iter.next(), Some((&3, &3)));
        assert_eq!(iter.next(), Some((&5, &5)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn remove_insert_on_heavy_load() {
        let count = 1_000_000;
        let mut map = Ommap::new();
        let mut is = Vec::with_capacity(count);
        let mut rs = Vec::with_capacity(count);
        for i in 0..count {
            is.push((i, i));
            rs.push(i);
        }

        map.insert_multi(is);
        assert_eq!(map.len(), count);

        map.remove_multi(&rs);
        assert_eq!(map.len(), 0);
    }


    #[test]
    fn into_iter() {
        let mut map = Ommap::new();
        map.push(3, 'c');
        map.push(1, 'a');
        map.push(2, 'b');

        let mut iter = map.into_iter();
        assert_eq!(iter.next(), Some((1, 'a')));
        assert_eq!(iter.next(), Some((2, 'b')));
        assert_eq!(iter.next(), Some((3, 'c')));
    }

    #[test]
    fn iter() {
        let mut map = Ommap::new();
        map.push(3, 'c');
        map.push(2, 'b');
        map.push(1, 'a');

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&1, &'a')));
        assert_eq!(iter.next(), Some((&2, &'b')));
        assert_eq!(iter.next(), Some((&3, &'c')));
    }


    #[test]
    fn iter_mut() {
        let mut map = Ommap::new();
        map.push(1, 'a');
        map.push(3, 'c');
        map.push(2, 'b');

        let mut iter = map.iter_mut();
        assert_eq!(iter.next(), Some((&1, &mut 'a')));
        assert_eq!(iter.next(), Some((&2, &mut 'b')));
        assert_eq!(iter.next(), Some((&3, &mut 'c')));
    }

    #[test]
    fn values() {
        let mut map = Ommap::new();
        map.push(3, 'c');
        map.push(2, 'b');
        map.push(1, 'a');

        let mut iter = map.values();
        assert_eq!(iter.next(), Some(&'a'));
        assert_eq!(iter.next(), Some(&'b'));
        assert_eq!(iter.next(), Some(&'c'));
    }


    #[test]
    fn values_mut() {
        let mut map = Ommap::new();
        map.push(3, 'c');
        map.push(2, 'b');
        map.push(1, 'a');

        let mut iter = map.values_mut();
        assert_eq!(iter.next(), Some(&mut 'a'));
        assert_eq!(iter.next(), Some(&mut 'b'));
        assert_eq!(iter.next(), Some(&mut 'c'));
    }

    #[test]
    fn keys() {
        let mut map = Ommap::new();
        map.push(3, 'c');
        map.push(2, 'b');
        map.push(1, 'a');

        let mut iter = map.keys();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
    }
}