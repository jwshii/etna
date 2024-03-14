from hypothesis import given, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, Leaf, Node


@st.composite
def bsts(draw, lo=-10, hi=10):
    if lo > hi:
        return Leaf()
    else:
        # Pick a number from a range, if 0 we just return a Leaf
        if not draw(st.integers(min_value=0, max_value=3)):
            return Leaf()

        x = draw(st.integers(min_value=lo, max_value=hi))
        return Node(x, draw(bsts(lo, x - 1)), draw(bsts(x + 1, hi)))


@given(bsts(), st.integers())
def test_insert_valid(t: Tree, x: int):
    spec.test_insert_valid(t, x)
