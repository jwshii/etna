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
def exprs(draw, ctx={}, ty=None, max_depth=3):
    good_vars = [k for k, v in ctx.items() if ty is None or v == ty]
    if len(good_vars) > 0 and not draw(st.integers(0, 5)):
        return draw(st.one_of([st.just(Var(x)) for x in good_vars]))

    if max_depth == 0:
        if ty is None:
            ty = draw(tys())
        match ty:
            case TInt():
                return draw(st.one_of(st.builds(Int, st.integers())))
            case TBool():
                return draw(st.builds(Bool, st.booleans()))
    else:
        if ty is None:
            ty = draw(tys())
        match ty:
            case TInt():
                return draw(st.one_of(
                    st.builds(Int, st.integers()),
                    st.builds(Add, exprs(ctx, TInt(), max_depth - 1), exprs(ctx, TInt(), max_depth - 1)),
                    st.builds(Mul, exprs(ctx, TInt(), max_depth - 1), exprs(ctx, TInt(), max_depth - 1)),
                ))
            case TBool():
                return draw(st.one_of(
                    st.builds(Bool, st.booleans()),
                    st.builds(LessThan, exprs(ctx, TInt(), max_depth - 1), exprs(ctx, TInt(), max_depth - 1)),
                    st.builds(And, exprs(ctx, TBool(), max_depth - 1), exprs(ctx, TBool(), max_depth - 1))
                ))
            case e:
                print(e)
                raise Exception("unreachable")

@st.composite
def programs(draw):
    assigns = []
    ctx = {}
    for _ in range(draw(st.integers(0, 10))):
        ty = draw(tys())
        v = draw(varnames())
        assigns.append((v, draw(exprs(ctx=ctx, ty=ty))))
        ctx[v] = ty
    return Program(assigns, draw(exprs(ctx=ctx)))


@given(programs())
@settings(max_examples=100,
          phases=[Phase.generate],
          suppress_health_check=HealthCheck.all())
def test_evaluate_equiv_to_python(p):
    spec.test_evaluate_equiv_to_python(p)
