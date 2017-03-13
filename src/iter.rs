pub trait ToFilterZip<B>: Sized {
    /// Zips the iterators by matching their keys against each other in ascending order
    /// and only yielding the equal ones.
    fn filter_zip(self, B) -> FilterZip<Self, B::IntoIter> where B: IntoIterator;
}

pub struct FilterZip<A, B> {
    a: A,
    b: B,
}

impl<K, V, W, A, B> Iterator for FilterZip<A, B>
    where K: Ord,
          A: Iterator,
          A::Item: Unpair<Left = K, Right = V>,
          B: Iterator,
          B::Item: Unpair<Left = K, Right = W>,
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

impl<K, V, W, A, B> ToFilterZip<B> for A
    where K: Ord,
          A: Iterator,
          A::Item: Unpair<Left = K, Right = V>,
          B: IntoIterator,
          B::Item: Unpair<Left = K, Right = W>,
{
    fn filter_zip(self, b: B) -> FilterZip<A, B::IntoIter> {
        FilterZip {
            a: self,
            b: b.into_iter(),
        }
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


    /////////////////////////////////////
    // Tests
    /////////////////////////////////////


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn filter_zip_vec() {
        let mut a = Vec::new();
        let mut b = Vec::new();

        a.push((0, 'a'));
        a.push((1, 'a'));

        b.push((1, 'b'));
        b.push((2, 'b'));

        {
            let mut iter = a.iter().filter_zip(b.iter());
            assert_eq!(iter.next(), Some((&1, (&'a', &'b'))));
            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = a.iter().filter_zip(b.iter_mut());
            assert_eq!(iter.next(), Some((&1, (&'a', &mut 'b'))));
            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = a.iter_mut().filter_zip(b.iter());
            assert_eq!(iter.next(), Some((&1, (&mut 'a', &'b'))));
            assert_eq!(iter.next(), None);
        }

        {
            let mut iter = a.iter_mut().filter_zip(b.iter_mut());
            assert_eq!(iter.next(), Some((&1, (&mut 'a', &mut 'b'))));
            assert_eq!(iter.next(), None);
        }

        let mut iter = a.into_iter().filter_zip(b.into_iter());
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

        let mut iter = a.iter().filter_zip(&mut b);
        assert_eq!(iter.next(), Some((&1, (&1, &mut 6))));
        assert_eq!(iter.next(), Some((&2, (&4, &mut 7))));
        assert_eq!(iter.next(), Some((&3, (&3, &mut 8))));
        assert_eq!(iter.next(), Some((&5, (&2, &mut 9))));
        assert_eq!(iter.next(), None);
    }
}