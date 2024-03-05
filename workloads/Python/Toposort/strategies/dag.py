import sys
from hypothesis import HealthCheck, Phase, given, settings, strategies as st

sys.path.append("..")
import spec
from impl import Graph


@st.composite
def graphs(draw):
    alphabet = "abcdefghijklmnopqrstuvwxyz"
    cutoff = draw(st.integers(min_value=0, max_value=26))
    vs = draw(st.permutations(alphabet[:cutoff]))
    g = Graph()
    for v in vs:
        g.add_node(v)
    for i in range(len(vs)):
        v = vs[i]
        for w in vs[i:]:
            if v != w and not (draw(st.integers(min_value=0, max_value=5))):
                g.add_edge(v, w)
    return g


@given(graphs())
@settings(phases=[Phase.generate], suppress_health_check=HealthCheck.all())
def test_toposort(g):
    spec.test_toposort(g)
