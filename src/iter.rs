use std::mem;

impl<K, V> ::Ommap<K, V> {
    pub fn multi<'a>(&'a self) -> Multi<'a, K, V> {
        Multi {
            keys: &self.keys,
            values: &self.values,
        }
    }

    pub fn multi_mut<'a>(&'a mut self) -> MultiMut<'a, K, V> {
        MultiMut {
            keys: &self.keys,
            values: &mut self.values,
        }
    }
}

pub struct Multi<'a, K: 'a, V: 'a> {
    keys: &'a [K],
    values: &'a [V],
}

impl<'a, K: PartialEq, V> Iterator for Multi<'a, K, V> {
    type Item = (&'a K, &'a [V]);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(key) = self.keys.first() {
            if let Some(len) = self.keys.iter().position(|k| k != key) {
                self.keys = &self.keys[len..];
                let (v, vs) = self.values.split_at(len);
                self.values = vs;
                return Some((key, v));
            }
            self.keys = &self.keys[..0];
            return Some((key, self.values));
        }
        None
    }
}

pub struct MultiMut<'a, K: 'a, V: 'a> {
    keys: &'a [K],
    values: &'a mut [V],
}

impl<'a, K: PartialEq, V> Iterator for MultiMut<'a, K, V> {
    type Item = (&'a K, &'a mut [V]);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(key) = self.keys.first() {
            if let Some(len) = self.keys.iter().position(|k| k != key) {
                self.keys = &self.keys[len..];
                return Some((key, unsafe {
                    let v = mem::transmute(&mut self.values[..len]);
                    self.values = mem::transmute(&mut self.values[len..]);
                    v
                }));
            }
            self.keys = &self.keys[..0];
            return Some((key, unsafe { mem::transmute(&mut self.values[..]) }));
        }
        None
    }
}


pub struct Group<T> {
    group: T,
}

pub fn group<T, U>(u: U) -> Group<T>
    where Group<T>: From<U>,
          Group<T>: Iterator,
{
    Group::from(u)
}

use std::cmp::max;
macro_rules! max {
    ($x:expr) => ( $x );
    ($x:expr, $($xs:expr),+) => {
        max($x, max!( $($xs),+ ))
    };
}

macro_rules! impl_group {
    ($($V:ident, $I:ident),+) => {
        #[allow(non_snake_case)]
        #[allow(unused_assignments)]
        impl<K, $($V,)* $($I,)*> Iterator for Group<($($I,)*)>
            where K: Ord + Copy,
                  $(
                    $I: Iterator,
                    $I::Item: Unpair<Left = K, Right = $V>,
                  )*
        {
            type Item = (K, $($V),*);

            fn next(&mut self) -> Option<Self::Item> {
                let ($(ref mut $I,)*) = self.group;
                if let ($(Some($V),)*) = ($($I.next(),)*) {
                    let ($(mut $V,)*) = ($($V.unpair(),)*);
                    loop {
                        let max = max!($($V.0),*);
                        if $($V.0 == max) && * {
                            return Some((max, $($V.1),*));
                        }
                        $(
                            while $V.0 < max {
                                if let Some(next) = $I.next() {
                                    $V = next.unpair();
                                } else {
                                    return None;
                                }
                            }
                        )*
                    }
                }
                None
            }
        }

        #[allow(non_snake_case)]
        impl<$($I: IntoIterator),*> From<($($I,)*)> for Group<($($I::IntoIter,)*)> {
            fn from(u: ($($I,)*)) -> Self {
                let ($($I,)*) = u;
                Group {
                    group: ($($I.into_iter(),)*)
                }
            }
        }
    };
}

impl_group!(V1, I1);
impl_group!(V1, I1, V2, I2);
impl_group!(V1, I1, V2, I2, V3, I3);
impl_group!(V1, I1, V2, I2, V3, I3, V4, I4);
impl_group!(V1, I1, V2, I2, V3, I3, V4, I4, V5, I5);
impl_group!(V1, I1, V2, I2, V3, I3, V4, I4, V5, I5, V6, I6);
impl_group!(V1, I1, V2, I2, V3, I3, V4, I4, V5, I5, V6, I6, V7, I7);


    /////////////////////////////////////
    // Helper
    /////////////////////////////////////


pub trait Unpair {
    type Left;
    type Right;

    #[inline]
    fn unpair(self) -> (Self::Left, Self::Right);
}

impl<T, U> Unpair for (T, U) {
    type Left = T;
    type Right = U;

    fn unpair(self) -> (T, U) {
        (self.0, self.1)
    }
}

impl<'a, T, U> Unpair for &'a (T, U) {
    type Left = &'a T;
    type Right = &'a U;

    fn unpair(self) -> (&'a T, &'a U) {
        (&self.0, &self.1)
    }
}

impl<'a, T, U> Unpair for &'a mut (T, U) {
    type Left = &'a T;
    type Right = &'a mut U;

    fn unpair(self) -> (&'a T, &'a mut U) {
        (&self.0, &mut self.1)
    }
}


    /////////////////////////////////////
    // Tests
    /////////////////////////////////////


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multi() {
        let map = ::Ommap::from(vec!((1, 0), (3, 1), (3, 2), (3, 3), (5, 0)));
        let mut iter = map.multi();
        assert_eq!(iter.next(), Some((&1, &[0][..])));
        assert_eq!(iter.next(), Some((&3, &[1, 2, 3][..])));
        assert_eq!(iter.next(), Some((&5, &[0][..])));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn multi_mut() {
        let mut map = ::Ommap::from(vec!((1, 0), (3, 1), (3, 2), (3, 3), (5, 0)));
        let mut iter = map.multi_mut();
        assert_eq!(iter.next(), Some((&1, &mut [0][..])));
        assert_eq!(iter.next(), Some((&3, &mut [1, 2, 3][..])));
        assert_eq!(iter.next(), Some((&5, &mut [0][..])));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn group_3() {
        let a =     vec![(1, 'a'), (2, 'f'), (3, 'a'), (4, 'b'), (5, 'a')];
        let b =     vec![          (2, 'i'),           (4, 'a'), (5, 'b')];
        let mut c = vec![(1, 'c'), (2, 'z'), (3, 'c'), (4, 'r')];
        let mut iter = group((&a, &b, &mut c));
        assert_eq!(iter.next(), Some((&2, &'f', &'i', &mut 'z')));
        assert_eq!(iter.next(), Some((&4, &'b', &'a', &mut 'r')));
        assert_eq!(iter.next(), None);
    }
}