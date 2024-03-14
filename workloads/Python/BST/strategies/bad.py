from hypothesis import given, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, Leaf


@given(st.just(Leaf()))
def test_insert_valid(t: Tree, x: int):
    spec.test_insert_valid(t, x)
