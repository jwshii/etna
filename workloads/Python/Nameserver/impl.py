class NameServer:
    names: dict[str, int] = {}

    def register(self, name: str, pid: int) -> None:
        self.names[name] = pid

    def unregister(self, name: str) -> None:
        self.names.pop(name, None)

    def where_is(self, name: str) -> int | None:
        return self.names.get(name)
