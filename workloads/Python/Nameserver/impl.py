class NameServer:
    names: dict[str, int]

    def __init__(self):
        self.names = {}

    def register(self, name: str, pid: int) -> None:
        if name in self.names:
            raise ValueError("Name already registered")
        #etna_base zero_pid
        self.names[name] = pid
        #etna_mutant zero_pid
        #self.names[name] = 0
        #etna_mutant_end zero_pid

    def unregister(self, name: str) -> None:
        if name not in self.names:
            raise ValueError("Name not registered")
        self.names.pop(name, None)

    def where_is(self, name: str) -> int | None:
        return self.names.get(name)
