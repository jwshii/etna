from hypothesis import Phase, given, settings, strategies as st
import sys

sys.path.append("..")
import spec
from impl import Tree, E, T, Red, Black


@st.composite
def trees(draw, max_depth=3):
    if max_depth == 0:
        return E()
    else:
        if not draw(st.booleans()):
            return E()
        return T(draw(st.one_of(st.just(Red()), st.just(Black()))),
                 draw(trees(max_depth - 1)), draw(st.integers()),
                 draw(st.integers()), draw(trees(max_depth - 1)))


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
