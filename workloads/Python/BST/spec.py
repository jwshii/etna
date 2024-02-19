from impl import *
from hypothesis import assume


def test_insert_valid(t: Tree, x: int):
    assume(t.is_binary_search_tree())
    assert t.insert(x).is_binary_search_tree()


def test_insert_post(t: Tree, x: int):
    assume(t.is_binary_search_tree())
    assert t.insert(x).contains(x)
