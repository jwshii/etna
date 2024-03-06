from hypothesis import Phase, given, settings, strategies as st
import sys

sys.path.append("..")
import spec
from impl import T, Black, Color, Red, Tree, E


def insert(k: int, v: int, t: Tree) -> Tree:
    def balance(col: Color, l: Tree, k: int, v: int, r: Tree) -> Tree:
        match (col, l, k, v, r):
            case (Black(), T(Red(), T(Red(), a, x, xv, b), y, yv, c), z, zv, d):
                return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
            case (Black(), T(Red(), a, x, xv, T(Red(), b, y, yv, c)), z, zv, d):
                return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
            case (Black(), a, x, xv, T(Red(), T(Red(), b, y, yv, c), z, zv, d)):
                return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
            case (Black(), a, x, xv, T(Red(), b, y, yv, T(Red(), c, z, zv, d))):
                return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
            case (_, _, _, _, _):
                return T(col, l, k, v, r)

    def blacken(t: Tree) -> Tree:
        if isinstance(t, E):
            return t
        elif isinstance(t, T):
            return T(Black(), t.l, t.k, t.v, t.r)
        else:
            raise Exception("impossible")

    def ins(t: Tree) -> Tree:
        if isinstance(t, E):
            return T(Red(), E(), k, v, E())

        elif isinstance(t, T):
            if k < t.k:
                return balance(t.c, ins(t.l), t.k, t.v, t.r)
            elif k > t.k:
                return balance(t.c, t.l, t.k, t.v, ins(t.r))
            return T(t.c, t.l, k, v, t.r)
        else:
            raise Exception("impossible")

    return blacken(ins(t))


@st.composite
def trees(draw):
    kvs = draw(st.lists(st.tuples(st.integers(), st.integers())))

    t = E()
    for (k, v) in kvs:
        t = insert(k, v, t)
    return t


@given(trees(), st.integers(), st.integers())
@settings(max_examples=100, phases=[Phase.generate])
def test_insert_valid(t: Tree, k: int, v: int):
    spec.test_insert_valid(t, k, v)

@given(trees(), st.integers(), st.integers())
@settings(max_examples=100, phases=[Phase.generate])
def test_insert_member(t: Tree, k: int, v: int):
    spec.test_insert_member(t, k, v)

@given(trees(), st.integers())
@settings(max_examples=100, phases=[Phase.generate])
def test_delete_valid(t: Tree, k: int):
    spec.test_delete_valid(t, k)

@given(trees(), st.integers())
@settings(max_examples=100, phases=[Phase.generate])
def test_delete_member(t: Tree, k: int):
    spec.test_delete_member(t, k)