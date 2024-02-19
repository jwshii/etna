from hypothesis import given, settings, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, E, T, Color


@st.composite
def trees(draw, max_depth=3):
    if max_depth == 0:
        return E()
    else:
        if not draw(st.integers(min_value=0, max_value=max_depth)):
            return E()
        return T(Color.red() if draw(st.booleans()) else Color.black(),
                 draw(trees(max_depth - 1)), draw(st.integers()),
                 draw(st.integers()), draw(trees(max_depth - 1)))


@given(trees(), st.integers(), st.integers())
@settings(max_examples=1000)
def test_insert_valid(t: Tree, k: int, v: int):
    spec.test_insert_valid(t, k, v)
