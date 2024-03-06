from hypothesis import Phase, given, settings, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, E, T, Red, Black


@st.composite
def trees(draw, lo=-10, hi=10):
    if lo > hi:
        return E()
    else:
        # Pick a number from a range, if 0 we just return a Leaf
        if not draw(st.integers(min_value=0, max_value=3)):
            return E()

        x = draw(st.integers(min_value=lo, max_value=hi))
        return T(Red() if draw(st.booleans()) else Black(),
                 draw(trees(lo, x - 1)), x, draw(st.integers()),
                 draw(trees(x + 1, hi)))


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
