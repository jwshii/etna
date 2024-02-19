from hypothesis import given
import sys

sys.path.append("..")
import spec
from impl import Tree


@given(...)
def test_insert_valid(t: Tree, x: int):
    spec.test_insert_valid(t, x)


@given(...)
def test_insert_post(t: Tree, x: int):
    spec.test_insert_post(t, x)
