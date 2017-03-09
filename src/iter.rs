pub struct FilterZip<A, B> {
    a: A,
    b: B,
}

pub trait ToFilterZip<B>: Sized {
    /// Zips the iterators by matching their keys against each other in ascending order
    /// and only yielding the equal ones.
    fn filter_zip(self, B) -> FilterZip<Self, B>;
}

impl<K, V, W, A, B> Iterator for FilterZip<A, B>
    where K: Ord,
          A: Iterator<Item=(K, V)>,
          B: Iterator<Item=(K, W)>,
{
    type Item = (K, (V, W));
    fn next(&mut self) -> Option<Self::Item> {
        if let (Some(mut a), Some(mut b)) = (self.a.next(), self.b.next()) {
            while a.0 != b.0 {
                if a.0 < b.0 {
                    if let Some(next) = self.a.next() {
                        a = next;
                    } else {
                        return None;
                    }
                } else {
                    if let Some(next) = self.b.next() {
                        b = next;
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


    /////////////////////////////////////
    // Tests
    /////////////////////////////////////


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ommap_filter_zip() {
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

        let mut iter = a.iter().filter_zip(b.iter_mut());
        assert_eq!(iter.next(), Some((&1, (&1, &mut 6))));
        assert_eq!(iter.next(), Some((&2, (&4, &mut 7))));
        assert_eq!(iter.next(), Some((&3, (&3, &mut 8))));
        assert_eq!(iter.next(), Some((&5, (&2, &mut 9))));
        assert_eq!(iter.next(), None);
    }
}