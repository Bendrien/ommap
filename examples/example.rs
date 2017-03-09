extern crate ommap;

use ommap::Ommap;

fn main() {
    println!("prepare");
    let count = 1_000_000;
    let mut map = Ommap::new();
    let mut is = Vec::with_capacity(count);
    let mut rs = Vec::with_capacity(count);
    for i in 0..count {
        is.push((i, i));
        rs.push(i);
    }

    println!("insert");
    map.insert_multi(is);

    println!("remove");
    map.remove_multi(&rs);

    print!("finish");
}