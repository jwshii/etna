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
    for i in range(len(vs)):
        g.add_node(vs[i])
        if i > 0:
            g.add_edge(vs[i - 1], vs[i])
    return g


@given(graphs())
@settings(phases=[Phase.generate], suppress_health_check=HealthCheck.all())
def test_toposort(g):
    spec.test_toposort(g)
