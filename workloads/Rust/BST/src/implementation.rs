#[derive(Debug, Clone)]
pub enum Tree {
    E,
    T(Box<Tree>, i32, i32, Box<Tree>),
}

use Tree::*;

const FUEL: usize = 10000;

// Insert
pub(crate) fn insert(k: i32, v: i32, t: Tree) -> Tree {
    match t {
        E => T(Box::new(E), k, v, Box::new(E)),
        T(l, k2, v2, r) => {
            /*| insert */
/*|
            if k < k2 {
                T(Box::new(insert(k, v, *l)), k2, v2, r)
            } else if k2 < k {
                T(l, k2, v2, Box::new(insert(k, v, *r)))
            } else {
                T(l, k2, v, r)
            }
*/
            /*|| insert_1 */
            /*|
            T(Box::new(E), k, v, Box::new(E))
            */
            /*|| insert_2 */
            if k < k2 {
                T(Box::new(insert(k, v, *l)), k2, v2, r)
            } else {
                T(l, k2, v, r)
            }
            /*|| insert_3 */
            /*|
            if k < k2 {
                T(Box::new(insert(k, v, *l)), k2, v2, r)
            } else if k2 < k {
                T(l, k2, v2, Box::new(insert(k, v, *r)))
            } else {
                T(l, k2, v2, r)
            }
            */
            /* |*/
        },
    }
}

// Join
pub(crate) fn join(l: Tree, r: Tree) -> Tree {
    match (l, r) {
        (E, r) => r,
        (l, E) => l,
        (T(l1, k1, v1, r1), T(l2, k2, v2, r2)) => {
            T(l1, k1, v1, Box::new(T(Box::new(join(*r1, *l2)), k2, v2, r2)))
        },
    }
}

// Delete
pub(crate) fn delete(k: i32, t: Tree) -> Tree {
    match t {
        E => E,
        T(l, k2, v2, r) => {
            // Default delete
            if k < k2 {
                T(Box::new(delete(k, *l)), k2, v2, r)
            } else if k2 < k {
                T(l, k2, v2, Box::new(delete(k, *r)))
            } else {
                join(*l, *r)
            }

            /*
            // delete_4
            let _ = v2;
            if k < k2 {
                delete(k, *l)
            } else if k2 < k {
                delete(k, *r)
            } else {
                join(*l, *r)
            }
            */

            /*
            // delete_5
            if k2 < k {
                T(Box::new(delete(k, *l)), k2, v2, r)
            } else if k < k2 {
                T(l, k2, v2, Box::new(delete(k, *r)))
            } else {
                join(*l, *r)
            }
            */
        },
    }
}

// Below
pub(crate) fn below(k: i32, t: Tree) -> Tree {
    match t {
        E => E,
        T(l, k2, v2, r) => {
            if k <= k2 {
                below(k, *l)
            } else {
                T(l, k2, v2, Box::new(below(k, *r)))
            }
        },
    }
}

// Above
pub(crate) fn above(k: i32, t: Tree) -> Tree {
    match t {
        E => E,
        T(l, k2, v2, r) => {
            if k2 <= k {
                above(k, *r)
            } else {
                T(Box::new(above(k, *l)), k2, v2, r)
            }
        },
    }
}

// Union with fuel
pub(crate) fn union_(l: Tree, r: Tree, f: usize) -> Tree {
    if f == 0 {
        return E;
    }
    let f1 = f - 1;
    match (l, r) {
        (E, r) => r,
        (l, E) => l,

        // Default union_
        (T(l1, k, v, r1), t) => {
            T(
                Box::new(union_(*l1, below(k, t.clone()), f1)),
                k,
                v,
                Box::new(union_(*r1, above(k, t), f1)),
            )
        }

        /*
        // union_6
        (T(l1, k1, v1, r1), T(l2, k2, v2, r2)) => {
            T(l1, k1, v1, Box::new(T(Box::new(union_(*r1, *l2, f1)), k2, v2, r2)))
        }
        */

        /*
        // union_7
        (T(l1, k1, v1, r1), T(l2, k2, v2, r2)) => {
            if k1 == k2 {
                T(
                    Box::new(union_(*l1, *l2, f1)),
                    k1,
                    v1,
                    Box::new(union_(*r1, *r2, f1)),
                )
            } else if k1 < k2 {
                T(
                    l1,
                    k1,
                    v1,
                    Box::new(T(Box::new(union_(*r1, *l2, f1)), k2, v2, r2)),
                )
            } else {
                union_(T(l2, k2, v2, r2), T(l1, k1, v1, r1), f1)
            }
        }
        */

        /*
        // union_8
        (T(l1, k1, v1, r1), T(l2, k2, v2, r2)) => {
            if k1 == k2 {
                T(
                    Box::new(union_(*l1, *l2, f1)),
                    k1,
                    v1,
                    Box::new(union_(*r1, *r2, f1)),
                )
            } else if k1 < k2 {
                T(
                    Box::new(union_(*l1, below(k1, *l2), f1)),
                    k1,
                    v1,
                    Box::new(union_(*r1, T(Box::new(above(k1, *l2)), k2, v2, r2), f1)),
                )
            } else {
                union_(T(l2, k2, v2, r2), T(l1, k1, v1, r1), f1)
            }
        }
        */
    }
}

pub(crate) fn union(l: Tree, r: Tree) -> Tree {
    union_(l, r, FUEL)
}

// Find
pub(crate) fn find(k: i32, t: &Tree) -> Option<i32> {
    match t {
        E => None,
        T(l, k2, v2, r) => {
            if k < *k2 {
                find(k, l)
            } else if *k2 < k {
                find(k, r)
            } else {
                Some(*v2)
            }
        },
    }
}

// Size
pub(crate) fn size(t: &Tree) -> usize {
    match t {
        E => 0,
        T(l, _, _, r) => 1 + size(l) + size(r),
    }
}
