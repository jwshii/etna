from hypothesis import strategies as st
from hypothesis.stateful import RuleBasedStateMachine, rule


class NameServer:
    names: dict[str, int] = {}

    def register(self, name: str, pid: int) -> None:
        self.names[name] = pid

    def unregister(self, name: str) -> None:
        self.names.pop(name, None)

    def where_is(self, name: str) -> int | None:
        return self.names.get(name)


class NameServerComparison(RuleBasedStateMachine):

    def __init__(self):
        super().__init__()
        self.model = {}
        self.ns = NameServer()

    @rule(name=st.text(), pid=st.integers())
    def register(self, name: str, pid: int):
        self.model[name] = pid
        self.ns.register(name, pid)

    @rule(name=st.text())
    def unregister(self, name: str):
        self.model.pop(name, None)
        self.ns.unregister(name)

    @rule(name=st.text())
    def where_is(self, name: str):
        assert self.ns.where_is(name) == self.model.get(name)

    def teardown(self):
        pass


def test_name_server():
    NameServerComparison.TestCase().runTest()
