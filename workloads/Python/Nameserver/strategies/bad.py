import sys
from hypothesis import assume, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, rule

sys.path.append("..")
from impl import NameServer


def names():
    return st.text(alphabet="abcdefghijklmnopqrstuvwxyz")


class NameServerComparison(RuleBasedStateMachine):

    def __init__(self):
        super().__init__()
        self.model = {}
        self.ns = NameServer()

    @rule(name=names(), pid=st.integers())
    def register(self, name: str, pid: int):
        try:
            self.ns.register(name, pid)
        except ValueError:
            assume(False)
        self.model[name] = pid

    @rule(name=names())
    def unregister(self, name: str):
        try:
            self.ns.unregister(name)
        except ValueError:
            assume(False)
        self.model.pop(name, None)

    @rule(name=names())
    def where_is(self, name: str):
        assert self.ns.where_is(name) == self.model.get(name)

    def teardown(self):
        pass


def test_name_server():
    NameServerComparison.TestCase().runTest()
