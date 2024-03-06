class NameServer:

    #etna_base bad_combination

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
        #etna_base forget_unregister
        self.names.pop(name, None)
        #etna_mutant forget_unregister
        #etna_mutant_end forget_unregister

    def where_is(self, name: str) -> int | None:
        #etna_base raise_if_missing
        return self.names.get(name)
        #etna_mutant raise_if_missing
        #return self.names[name]
        #etna_mutant_end raise_if_missing


#etna_mutant bad_combination
#    names: dict[str, int]
#    registered: set[str]
#    unregistered: set[str]
#
#    def __init__(self):
#        self.names = {}
#    def register(self, name: str, pid: int) -> None:
#        if name in self.names:
#            raise ValueError("Name already registered")
#        self.names[name] = pid
#        self.registered.add(name)
#
#    def unregister(self, name: str) -> None:
#        if name not in self.names:
#            raise ValueError("Name not registered")
#        self.names.pop(name, None)
#        self.unregistered.add(name)
#
#    def where_is(self, name: str) -> int | None:
#        if name in self.registered and name in self.unregistered:
#            raise Exception("It was here a minute ago!")
#        return self.names.get(name)
#etna_mutant_end bad_combination
