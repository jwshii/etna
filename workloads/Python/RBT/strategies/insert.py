from hypothesis import given, settings, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, E, insert


@st.composite
def trees(draw):
    kvs = draw(st.lists(st.tuples(st.integers(), st.integers())))

    t = E()
    for (k, v) in kvs:
        t = insert(k, v, t)
    return t


@given(trees(), st.integers(), st.integers())
@settings(max_examples=1000)
def test_insert_valid(t: Tree, k: int, v: int):
    spec.test_insert_valid(t, k, v)
