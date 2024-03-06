import sys
from hypothesis import HealthCheck, Phase, given, settings, strategies as st

sys.path.append("..")
import spec
from impl import *


def varnames():
    return st.one_of([st.just(c) for c in "abcdefghijklmnopqrstuvwxyz"])


def tys():
    return st.one_of(st.just(TInt()), st.just(TBool()))


@st.composite
def exprs(draw, ty=None, max_depth=3):
    if max_depth == 0:
        if ty is None:
            ty = draw(tys())
        match ty:
            case TInt():
                return draw(st.builds(Int, st.integers()))
            case TBool():
                return draw(st.builds(Bool, st.booleans()))
    else:
        if ty is None:
            ty = draw(tys())
        match ty:
            case TInt():
                return draw(st.one_of(
                    st.builds(Int, st.integers()),
                    st.builds(Add, exprs(TInt(), max_depth - 1), exprs(TInt(), max_depth - 1)),
                    st.builds(Mul, exprs(TInt(), max_depth - 1), exprs(TInt(), max_depth - 1)),
                ))
            case TBool():
                return draw(st.one_of(
                    st.builds(Bool, st.booleans()),
                    st.builds(LessThan, exprs(TInt(), max_depth - 1), exprs(TInt(), max_depth - 1)),
                    st.builds(And, exprs(TBool(), max_depth - 1), exprs(TBool(), max_depth - 1))
                ))
            case e:
                print(e)
                raise Exception("unreachable")

@st.composite
def programs(draw):
    return Program(
        draw(st.lists(st.tuples(varnames(), exprs()))),
        draw(exprs()),
    )


@given(programs())
@settings(max_examples=100,
          phases=[Phase.generate],
          suppress_health_check=HealthCheck.all())
def test_evaluate_equiv_to_python(p):
    spec.test_evaluate_equiv_to_python(p)
