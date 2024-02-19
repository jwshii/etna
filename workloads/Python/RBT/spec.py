from impl import *
from hypothesis import assume, event


def size(t: Tree) -> int:
    if isinstance(t, E):
        return 0
    elif isinstance(t, T):
        return 1 + size(t.l) + size(t.r)
    else:
        raise Exception("impossible")


def black_height(t: Tree) -> int:
    if isinstance(t, E):
        return 0
    elif isinstance(t, T):
        return (1 if t.c.is_black() else 0) + max(black_height(t.l),
                                                  black_height(t.r))
    else:
        raise Exception("impossible")


def test_insert_valid(t: Tree, k: int, v: int):
    event("size", payload=size(t))
    event("black_height", payload=black_height(t))
    assume(is_rbt(t))
    assert is_rbt(insert(k, v, t))
