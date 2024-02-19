from abc import ABC, abstractmethod
from dataclasses import dataclass


class Tree(ABC):

    @abstractmethod
    def size(self) -> int:
        pass

    @abstractmethod
    def depth(self) -> int:
        pass

    @abstractmethod
    def balanced(self) -> bool:
        pass

    @abstractmethod
    def lean(self) -> str:
        pass

    @abstractmethod
    def insert(self, x: int) -> "Tree":
        pass

    @abstractmethod
    def delete(self, x: int) -> "Tree":
        pass

    @abstractmethod
    def union(self, other: "Tree") -> "Tree":
        pass

    @abstractmethod
    def is_binary_search_tree(self) -> bool:
        pass

    @abstractmethod
    def to_list(self) -> list[int]:
        pass

    @abstractmethod
    def contains(self, v: int) -> bool:
        pass


@dataclass
class Node(Tree):
    value: int
    left: Tree
    right: Tree

    def size(self):
        return 1 + self.left.size() + self.right.size()

    def depth(self):
        return 1 + max(self.left.depth(), self.right.depth())

    def balanced(self):
        return abs(self.left.depth() - self.right.depth()) <= 1

    def lean(self):
        if self.left.depth() > self.right.depth():
            return "left"
        elif self.left.depth() < self.right.depth():
            return "right"
        else:
            return "none"

#etna_base insert_1
#etna_base insert_2

    def insert(self, x: int) -> "Tree":
        if x < self.value:
            return Node(self.value, self.left.insert(x), self.right)
        elif x > self.value:
            return Node(self.value, self.left, self.right.insert(x))
        else:
            return self


#etna_mutant insert_1
#    def insert(self, x: int) -> "Tree":
#        if x > self.value:
#            return Node(self.value, self.left.insert(x), self.right)
#        elif x < self.value:
#            return Node(self.value, self.left, self.right.insert(x))
#        else:
#            return self
#etna_mutant_end insert_1
#etna_mutant insert_2
#    def insert(self, x: int) -> "Tree":
#        return self
#etna_mutant_end insert_2

    def delete(self, x: int) -> "Tree":
        if x < self.value:
            return Node(self.value, self.left.delete(x), self.right)
        elif x > self.value:
            return Node(self.value, self.left, self.right.delete(x))
        else:
            return self.left.union(self.right)

    def to_list(self) -> list[int]:
        return self.left.to_list() + [self.value] + self.right.to_list()

    def is_binary_search_tree(self) -> bool:
        return self.left.is_binary_search_tree(
        ) and self.right.is_binary_search_tree() and all(
            x < self.value for x in self.left.to_list()) and all(
                x > self.value for x in self.right.to_list())

    def union(self, other: "Tree") -> "Tree":
        raise Exception("Not implemented")

    def contains(self, v: int) -> bool:
        if v < self.value:
            return self.left.contains(v)
        elif v > self.value:
            return self.right.contains(v)
        else:
            return True


@dataclass
class Leaf(Tree):

    def size(self):
        return 0

    def depth(self):
        return 0

    def balanced(self):
        return True

    def lean(self):
        return "none"

    def insert(self, x: int) -> "Tree":
        return Node(x, Leaf(), Leaf())

    def delete(self, x: int) -> "Tree":
        return self

    def union(self, other: "Tree") -> "Tree":
        return other

    def to_list(self) -> list[int]:
        return []

    def is_binary_search_tree(self) -> bool:
        return True

    def contains(self, v: int) -> bool:
        return False
