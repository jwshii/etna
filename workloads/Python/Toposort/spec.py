from hypothesis import assume, event
from impl import *


def test_toposort(g: Graph):
    assume(not g.has_cycles())
    event("len", len(g))
    if g.nodes:
        event("max_out_degree", max(len(g.neighbors(n)) for n in g.nodes))
    vs = g.toposort()
    for v, w in g.edges:
        assert vs.index(v) < vs.index(w)
