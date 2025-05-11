use {
    implementation::Tree,
    quickcheck::{par_quickcheck, quickcheck, Arbitrary},
    spec::{prop_insert_post, prop_insert_valid},
};

pub mod implementation;
pub mod spec;

fn gen_tree(g: &mut quickcheck::Gen, size: usize, lo: i32, hi: i32) -> Tree {
    if size == 0 || lo + 1 >= hi - 1 {
        return Tree::E;
    }

    let k = g.random_range(lo + 1..hi - 1);
    let left = gen_tree(g, size - 1, lo, k);
    let right = gen_tree(g, size - 1, k, hi);
    Tree::T(Box::new(left), k, k, Box::new(right))
}

impl Arbitrary for Tree {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let size = (g.size() as f64).log2() as usize;
        let lo = 0;
        let hi = 10;
        gen_tree(g, size, lo, hi)
    }
}

fn main() {
    par_quickcheck(prop_insert_post as fn(Tree, i32, i32, i32) -> bool);
}
