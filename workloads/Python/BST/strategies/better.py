from hypothesis import given, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, Leaf, Node


@st.composite
def trees(draw, max_depth=1):
    if max_depth == 0:
        return Leaf()
    else:
        if not draw(st.integers(min_value=0, max_value=max_depth)):
            return Leaf()
        return Node(draw(st.integers()), draw(trees(max_depth - 1)),
                    draw(trees(max_depth - 1)))


@given(trees(), st.integers())
def test_insert_valid(t: Tree, x: int):
    spec.test_insert_valid(t, x)
