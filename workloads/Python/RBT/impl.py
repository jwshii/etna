from __future__ import annotations
from abc import ABC
from dataclasses import dataclass
from typing import Tuple


@dataclass
class Color:
    _is_red: bool

    @staticmethod
    def red() -> Color:
        return Color(True)

    @staticmethod
    def black() -> Color:
        return Color(False)

    def is_red(self) -> bool:
        return self._is_red

    def is_black(self) -> bool:
        return not self._is_red


class Tree(ABC):
    pass


@dataclass
class E(Tree):
    pass


@dataclass
class T(Tree):
    c: Color
    l: Tree
    k: int
    v: int
    r: Tree


def keys(t: Tree) -> list[int]:
    if isinstance(t, E):
        return []
    elif isinstance(t, T):
        return keys(t.l) + [t.k] + keys(t.r)
    else:
        raise Exception("impossible")


def is_bst(t: Tree) -> bool:
    if isinstance(t, E):
        return True
    elif isinstance(t, T):
        return is_bst(t.l) and is_bst(t.r) and all(
            map(lambda y: y < t.k, keys(t.l))) and all(
                map(lambda y: y > t.k, keys(t.r)))
    else:
        raise Exception("impossible")


def has_black_root(t: Tree) -> bool:
    if isinstance(t, E):
        return True
    elif isinstance(t, T):
        return t.c.is_black()
    else:
        raise Exception("impossible")


def has_consistent_black_height(t: Tree) -> bool:

    def go(t: Tree) -> Tuple[bool, int]:
        if isinstance(t, E):
            return (True, 1)
        elif isinstance(t, T):
            (l_check, l_height) = go(t.l)
            (r_check, r_height) = go(t.r)
            t_is_black = 0 if t.c.is_red() else 1
            return (l_check and r_check
                    and l_height == r_height, l_height + t_is_black)
        else:
            raise Exception("impossible")

    return go(t)[0]


def has_no_red_red(t: Tree) -> bool:
    if isinstance(t, E):
        return True
    elif isinstance(t, T) and t.c.is_black():
        return has_no_red_red(t.l) and has_no_red_red(t.r)
    elif isinstance(t, T) and t.c.is_red():
        return has_black_root(t.l) and has_black_root(t.r) and has_no_red_red(
            t.l) and has_no_red_red(t.r)
    else:
        raise Exception("impossible")


def is_rbt(t: Tree) -> bool:
    return is_bst(t) and has_black_root(t) and has_consistent_black_height(
        t) and has_no_red_red(t)


def insert(k: int, v: int, t: Tree) -> Tree:

    def blacken(t: Tree) -> Tree:
        if isinstance(t, E):
            return t
        elif isinstance(t, T):
            return T(Color.black(), t.l, t.k, t.v, t.r)
        else:
            raise Exception("impossible")

    def ins(t: Tree) -> Tree:
        if isinstance(t, E):
            #etna_base miscolor_insert
            return T(Color.red(), E(), k, v, E())


#etna_mutant miscolor_insert
#            return T(Color.black(), E(), k, v, E())
#etna_mutant_end miscolor_insert
        elif isinstance(t, T):
            if k < t.k:
                return balance(t.c, ins(t.l), t.k, t.v, t.r)
            elif k > t.k:
                return balance(t.c, t.l, t.k, t.v, ins(t.r))
            return T(t.c, t.l, k, v, t.r)
        else:
            raise Exception("impossible")

    return blacken(ins(t))


def balance(c: Color, l: Tree, k: int, v: int, r: Tree) -> Tree:
    if c.is_black() and isinstance(l, T) and isinstance(
            l.l, T) and l.c.is_red() and l.l.c.is_red():
        return T(Color.red(), T(Color.black(), l.l.l, l.l.k, l.l.v, l.l.r),
                 l.k, l.v, T(Color.black(), l.r, k, v, r))
    elif c.is_black() and isinstance(l, T) and isinstance(
            l.r, T) and l.c.is_red() and l.r.c.is_red():
        return T(Color.red(), T(Color.black(), l.l, l.k, l.v, l.r.l), l.r.k,
                 l.r.v, T(Color.black(), l.r.r, k, v, r))
    elif c.is_black() and isinstance(r, T) and isinstance(
            r.l, T) and r.c.is_red() and r.l.c.is_red():
        return T(Color.red(), T(Color.black(), l, k, v, r.l.l), r.l.k, r.l.v,
                 T(Color.black(), r.l.r, r.k, r.v, r.r))
    elif c.is_black() and isinstance(r, T) and isinstance(
            r.r, T) and r.c.is_red() and r.r.c.is_red():
        return T(Color.red(), T(Color.black(), l, k, v, r.l), r.k, r.v,
                 T(Color.black(), r.r.r, r.r.k, r.r.v, r.r.r))
    return T(c, l, k, v, r)
