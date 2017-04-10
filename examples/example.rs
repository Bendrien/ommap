extern crate ommap;

use ommap::Ommap;
use ommap::iter::group;

fn main() {
    let a = Ommap::from(vec!((1,"a1"),(2,"a2"),(3,"a3"),(4,"a4"),(5,"a5"),(6,"a6")));
    let mut b = Ommap::from(vec!((1,"b1"),(2,"b2"),(3,"b3"),(4,"b4"),(5,"b5"),(6,"b6")));
    let c = Ommap::from(vec!((1,"c1"),(2,"c2"),(3,"c3"),(4,"c4"),(5,"c5"),(6,"c6")));

    for (_, a, b, c) in group((&a, &mut b, &c)) {
        println!("{}{}{}", a,b,c);
        *b = "  ";
        println!("{}{}{}", c,b,a);
    }
}