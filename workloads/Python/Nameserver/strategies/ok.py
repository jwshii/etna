import sys
from hypothesis import assume, event, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, rule

sys.path.append("..")
from impl import NameServer


def names():
    return st.text(alphabet="abcdefghijklmnopqrstuvwxyz")


class NameServerComparison(RuleBasedStateMachine):

    def __init__(self):
        super().__init__()
        self.model = {}
        self.counter = 0
        self.failures = 0
        self.ns = NameServer()

    @rule(name=names(), pid=st.integers())
    def register(self, name: str, pid: int):
        try:
            self.ns.register(name, pid)
        except ValueError:
            assert name in self.model
            self.failures += 1
            return
        self.model[name] = pid
        self.counter += 1

    @rule(name=names())
    def unregister(self, name: str):
        try:
            self.ns.unregister(name)
        except ValueError:
            assert name not in self.model
            self.failures += 1
            return
        self.model.pop(name, None)
        self.counter += 1

    @rule(name=names())
    def where_is(self, name: str):
        assert self.ns.where_is(name) == self.model.get(name)
        self.counter += 1

    def teardown(self):
        event("len", self.counter)
        event("failures", self.failures)


def test_name_server():
    NameServerComparison.TestCase().runTest()
