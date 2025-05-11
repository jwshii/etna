use crate::bst::*;

fn tree_eq(t1: &Tree, t2: &Tree) -> bool {
    to_list(t1) == to_list(t2)
}

fn keys(t: &Tree) -> Vec<i32> {
    match t {
        Tree::E => vec![],
        Tree::T(l, k, _, r) => {
            let mut result = vec![*k];
            result.extend(keys(l));
            result.extend(keys(r));
            result
        }
    }
}

fn all<T, F>(xs: &[T], f: F) -> bool
where
    F: Fn(&T) -> bool,
{
    xs.iter().all(f)
}

fn is_bst(t: &Tree) -> bool {
    match t {
        Tree::E => true,
        Tree::T(l, k, _, r) => {
            is_bst(l)
                && is_bst(r)
                && all(&keys(l), |k2| *k2 < *k)
                && all(&keys(r), |k2| *k2 > *k)
        }
    }
}

fn to_list(t: &Tree) -> Vec<(i32, i32)> {
    match t {
        Tree::E => vec![],
        Tree::T(l, k, v, r) => {
            let mut result = to_list(l);
            result.push((*k, *v));
            result.extend(to_list(r));
            result
        }
    }
}

fn delete_key(k: i32, xs: &[(i32, i32)]) -> Vec<(i32, i32)> {
    xs.iter().filter(|(x, _)| *x != k).cloned().collect()
}

fn l_insert((k, v): (i32, i32), xs: &[(i32, i32)]) -> Vec<(i32, i32)> {
    let mut inserted = false;
    let mut result = Vec::with_capacity(xs.len() + 1);
    for &(k2, v2) in xs {
        if !inserted && k < k2 {
            result.push((k, v));
            inserted = true;
        }
        if k == k2 && !inserted {
            result.push((k, v));
            inserted = true;
        } else {
            result.push((k2, v2));
        }
    }
    if !inserted {
        result.push((k, v));
    }
    result
}

fn sorted(xs: &[(i32, i32)]) -> bool {
    xs.windows(2).all(|w| w[0].0 < w[1].0)
}

fn l_sort(xs: &[(i32, i32)]) -> Vec<(i32, i32)> {
    let mut result = vec![];
    for &(k, v) in xs {
        result = l_insert((k, v), &result);
    }
    result
}

fn l_find(k: i32, xs: &[(i32, i32)]) -> Option<i32> {
    xs.iter().find(|(k2, _)| *k2 == k).map(|(_, v)| *v)
}

fn l_union_by<F>(f: F, l1: &[(i32, i32)], l2: &[(i32, i32)]) -> Vec<(i32, i32)>
where
    F: Fn(i32, i32) -> i32,
{
    let mut result = l2.to_vec();
    for &(k, v) in l1 {
        result.retain(|(k2, _)| *k2 != k);
        let v2 = l_find(k, l2).map(|v2| f(v, v2)).unwrap_or(v);
        result = l_insert((k, v2), &result);
    }
    result
}

pub fn prop_insert_valid(t: Tree, k: i32, v: i32) -> bool {
    is_bst(&t) && is_bst(&insert(k, v, t))
}

pub fn prop_delete_valid(t: &Tree, k: i32) -> bool {
    is_bst(t) && is_bst(&delete(k, t.clone()))
}

pub fn prop_union_valid(t1: &Tree, t2: &Tree) -> bool {
    is_bst(t1) && is_bst(t2) && is_bst(&union(t1.clone(), t2.clone()))
}

pub fn prop_insert_post(t: Tree, k: i32, k2: i32, v: i32) -> bool {
    is_bst(&t)
        && find(k2, &insert(k, v, t.clone()))
            == if k == k2 { Some(v) } else { find(k2, &t) }
}

pub fn prop_delete_post(t: &Tree, k: i32, k2: i32) -> bool {
    is_bst(t)
        && find(k2, &delete(k, t.clone()))
            == if k == k2 { None } else { find(k2, t) }
}

pub fn prop_union_post(t1: &Tree, t2: &Tree, k: i32) -> bool {
    is_bst(t1) && is_bst(t2) && {
        let lhs = find(k, &union(t1.clone(), t2.clone()));
        let rhs = find(k, t1);
        let rhs2 = find(k, t2);
        lhs == rhs.or(rhs2)
    }
}

pub fn prop_insert_model(t: &Tree, k: i32, v: i32) -> bool {
    is_bst(t)
        && to_list(&insert(k, v, t.clone()))
            == l_insert((k, v), &delete_key(k, &to_list(t)))
}

pub fn prop_delete_model(t: &Tree, k: i32) -> bool {
    is_bst(t) && to_list(&delete(k, t.clone())) == delete_key(k, &to_list(t))
}

pub fn prop_union_model(t1: &Tree, t2: &Tree) -> bool {
    is_bst(t1)
        && is_bst(t2)
        && to_list(&union(t1.clone(), t2.clone()))
            == l_sort(&l_union_by(|x, _| x, &to_list(t1), &to_list(t2)))
}
