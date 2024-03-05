import sys
from hypothesis import HealthCheck, Phase, given, settings, strategies as st

sys.path.append("..")
import spec
from impl import *


def vars():
    return st.one_of(st.just("x"), st.just("y"), st.just("z"))


def exprs():
    return st.recursive(
        st.one_of(
            st.builds(Int, st.integers()),
            st.builds(Bool, st.booleans()),
            st.builds(Var, vars()),
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
        draw(st.lists(st.tuples(vars(), exprs()))),
        draw(exprs()),
    )


@given(programs())
@settings(max_examples=10,
          phases=[Phase.generate],
          suppress_health_check=HealthCheck.all())
def test_evaluate_equiv_to_python(p):
    spec.test_evaluate_equiv_to_python(p)
