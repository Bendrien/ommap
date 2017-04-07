use std::iter::Peekable;

pub trait ToFilterZip<B>: Sized {
    /// Zips the iterators by matching their keys against each other in ascending order
    /// and only yielding the equal ones.
    fn fiz(self, B) -> FilterZip<Self, B::IntoIter> where B: IntoIterator;
}

pub struct FilterZip<A, B> {
    a: A,
    b: B,
}

impl<K, L, V, W, A, B> Iterator for FilterZip<A, B>
    where
        K: PartialOrd<L>,
        A: Iterator,
        A::Item: Unpair<Left = K, Right = V>,
        B: Iterator,
        B::Item: Unpair<Left = L, Right = W>,
{
    type Item = (K, (V, W));
    fn next(&mut self) -> Option<Self::Item> {
        if let (Some(a), Some(b)) = (self.a.next(), self.b.next()) {
            let (mut a, mut b) = (a.unpair(), b.unpair());
            while a.0 != b.0 {
                if a.0 < b.0 {
                    if let Some(next) = self.a.next() {
                        a = next.unpair();
                    } else {
                        return None;
                    }
                } else {
                    if let Some(next) = self.b.next() {
                        b = next.unpair();
                    } else {
                        return None;
                    }
                }
            }
            return Some((a.0, (a.1, b.1)));
        }
        None
    }
}

impl<K, L, V, W, A, B> ToFilterZip<B> for A
    where
        K: PartialOrd<L>,
        A: Iterator,
        A::Item: Unpair<Left = K, Right = V>,
        B: IntoIterator,
        B::Item: Unpair<Left = L, Right = W>,
{
    fn fiz(self, b: B) -> FilterZip<A, B::IntoIter> {
        FilterZip {
            a: self,
            b: b.into_iter(),
        }
    }
}

pub trait ToFilterCount<T: Iterator> {
    fn filter_count(self) -> FilterCount<T>;
}

pub struct FilterCount<I: Iterator> {
    iter: Peekable<I>,
}

impl<I: Iterator> Iterator for FilterCount<I> where I::Item: PartialEq {
    type Item = (I::Item, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let mut cnt = 1;
        while let Some(item) = self.iter.next() {
            if let Some(peek) = self.iter.peek() {
                if item == *peek {
                    cnt += 1;
                    continue;
                }
            }
            return Some((item, cnt));
        }
        None
    }
}

impl<I: Iterator> ToFilterCount<I> for I {
    fn filter_count(self) -> FilterCount<I> {
        FilterCount { iter: self.peekable() }
    }
}


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


trait Flatten<T> {
    fn flatten(self) -> T;
}

impl<A, B, C> Flatten<(A, B, C)> for (A, (B, C)) {
    fn flatten(self) -> (A, B, C) {
        let (a, (b, c)) = self;
        (a, b, c)
    }
}

impl<A, B, C, D> Flatten<(A, B, C, D)> for (A, ((B, C), D)) {
    fn flatten(self) -> (A, B, C, D) {
        let (a, ((b, c), d)) = self;
        (a, b, c, d)
    }
}

impl<A, B, C, D, E> Flatten<(A, B, C, D, E)> for (A, (((B, C), D), E)) {
    fn flatten(self) -> (A, B, C, D, E) {
        let (a, (((b, c), d), e)) = self;
        (a, b, c, d, e)
    }
}

impl<A, B, C, D, E, F> Flatten<(A, B, C, D, E, F)> for (A, ((((B, C), D), E), F)) {
    fn flatten(self) -> (A, B, C, D, E, F) {
        let (a, ((((b, c), d), e), f)) = self;
        (a, b, c, d, e, f)
    }
}

impl<A, B, C, D, E, F, G> Flatten<(A, B, C, D, E, F, G)> for (A, (((((B, C), D), E), F), G)) {
    fn flatten(self) -> (A, B, C, D, E, F, G) {
        let (a, (((((b, c), d), e), f), g)) = self;
        (a, b, c, d, e, f, g)
    }
}


    /////////////////////////////////////
    // Tests
    /////////////////////////////////////


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flatten() {
        assert_eq!(('a', (2usize, 3u8)).flatten(), ('a', 2, 3));
        assert_eq!(
            Flatten::<(_,_,_,_)>::flatten(('a', ((2, 3), 'd'))),
            ('a', 2, 3, 'd'));
        assert_eq!(
            Flatten::<(_,_,_,_,_)>::flatten(('a', (((2, 3), 'd'), 'e'))),
            ('a', 2, 3, 'd', 'e'));
        assert_eq!(
            Flatten::<(_,_,_,_,_,_)>::flatten(('a', ((((2, 3), 'd'), 'e'), 'f'))),
            ('a', 2, 3, 'd', 'e', 'f'));
        assert_eq!(
            Flatten::<(_,_,_,_,_,_,_)>::flatten(('a', (((((2, 3), 'd'), 'e'), 'f'), 'g'))),
            ('a', 2, 3, 'd', 'e', 'f', 'g'));


        use Ommap;

        // (Key, A, B)
        let a = Ommap::from(vec!((1,'a'), (2,'a'), (3,'a')));
        let b = Ommap::from(vec!((1,'b'), (2,'b'), (3,'b')));
        let mut iter = a.iter().fiz(&b);

        assert_eq!(iter.next().unwrap().flatten(), (&1, &'a', &'b'));
        assert_eq!(iter.next().unwrap().flatten(), (&2, &'a', &'b'));
        assert_eq!(iter.next().unwrap().flatten(), (&3, &'a', &'b'));
        assert_eq!(iter.next(), None);

        // (Key, A, B, C)
        let a = Ommap::from(vec!((1u8,'a'), (2,'a'), (3,'a')));
        let b = Ommap::from(vec!((1u8,'b'), (2,'b'), (3,'b')));
        let mut c = Ommap::from(vec!((1u8,'c'), (2,'c'), (3,'c')));
        let mut iter = a.iter().fiz(&b).fiz(&mut c);

        assert_eq!(
            Flatten::<(_,_,_,_)>::flatten(iter.next().unwrap()),
            (&1, &'a', &'b', &mut 'c'));
        assert_eq!(
            Flatten::<(_,_,_,_)>::flatten(iter.next().unwrap()),
            (&2, &'a', &'b', &mut 'c'));
        assert_eq!(
            Flatten::<(_,_,_,_)>::flatten(iter.next().unwrap()),
            (&3, &'a', &'b', &mut 'c'));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn filter_zip_vec() {
        let mut a = Vec::new();
        let mut b = Vec::new();

        a.push((0, 'a'));
        a.push((1, 'a'));

        b.push((1, 'b'));
        b.push((2, 'b'));

        {
            let mut iter = a.iter().fiz(b.iter());
            assert_eq!(iter.next(), Some((&1, (&'a', &'b'))));
            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = a.iter().fiz(b.iter_mut());
            assert_eq!(iter.next(), Some((&1, (&'a', &mut 'b'))));
            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = a.iter_mut().fiz(b.iter());
            assert_eq!(iter.next(), Some((&1, (&mut 'a', &'b'))));
            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = a.iter_mut().fiz(b.iter_mut());
            assert_eq!(iter.next(), Some((&1, (&mut 'a', &mut 'b'))));
            assert_eq!(iter.next(), None);
        }

        let mut iter = a.into_iter().fiz(b.into_iter());
        assert_eq!(iter.next(), Some((1, ('a', 'b'))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn filter_zip_ommap() {
        use Ommap;

        let mut a = Ommap::new();
        let mut b = Ommap::new();
        a.push(1, 1);
        a.push(1, 5);
        b.push(1, 6);
        a.push(2, 4);
        b.push(2, 7);
        a.push(3, 3);
        b.push(3, 8);
        a.push(5, 2);
        b.push(5, 9);

        let mut iter = a.iter().fiz(&mut b);
        assert_eq!(iter.next(), Some((&1, (&1, &mut 6))));
        assert_eq!(iter.next(), Some((&2, (&4, &mut 7))));
        assert_eq!(iter.next(), Some((&3, (&3, &mut 8))));
        assert_eq!(iter.next(), Some((&5, (&2, &mut 9))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn filter_count() {
        let v = vec!(1,
                     2, 2,
                     3, 3, 3,
                     4, 4, 4, 4,
                     5, 5, 5, 5, 5);
        let mut iter = v.iter().filter_count();
        assert_eq!(iter.next(), Some((&1, 1)));
        assert_eq!(iter.next(), Some((&2, 2)));
        assert_eq!(iter.next(), Some((&3, 3)));
        assert_eq!(iter.next(), Some((&4, 4)));
        assert_eq!(iter.next(), Some((&5, 5)));
        assert_eq!(iter.next(), None);
    }
}