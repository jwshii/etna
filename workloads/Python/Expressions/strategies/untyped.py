import sys
from hypothesis import HealthCheck, Phase, given, settings, strategies as st

sys.path.append("..")
import spec
from impl import *


def varnames():
    return st.one_of([st.just(c) for c in "abcdefghijklmnopqrstuvwxyz"])


def exprs():
    return st.recursive(
        st.one_of(
            st.builds(Int, st.integers()),
            st.builds(Bool, st.booleans()),
            st.builds(Var, varnames()),
        ),
        lambda children: st.one_of(
            st.builds(Var, st.text()),
            st.builds(Add, children, children),
            st.builds(Mul, children, children),
            st.builds(Bool, st.booleans()),
            st.builds(LessThan, children, children),
            st.builds(And, children, children),
        ),
    )


@st.composite
def programs(draw):
    return Program(
        draw(st.lists(st.tuples(varnames(), exprs()))),
        draw(exprs()),
    )


@given(programs())
@settings(max_examples=10,
          phases=[Phase.generate],
          suppress_health_check=HealthCheck.all())
def test_evaluate_equiv_to_python(p):
    spec.test_evaluate_equiv_to_python(p)
