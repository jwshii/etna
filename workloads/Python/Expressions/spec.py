from hypothesis import assume, event
from impl import *


def test_evaluate_equiv_to_python(p: Program):
    assume(infer_type(p) is not None)
    event("variable_uses", variable_uses(p))
    match evaluate(p):
        case VInt(v):
            assert v == python_evaluate(p)
        case VBool(v):
            assert v == python_evaluate(p)
        case _:
            assert False
