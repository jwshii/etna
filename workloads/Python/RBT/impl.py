from __future__ import annotations
from abc import ABC
from dataclasses import dataclass
from typing import Tuple


class Color(ABC):

    def is_black(self) -> bool:
        return isinstance(self, Black)

    def is_red(self) -> bool:
        return isinstance(self, Red)


@dataclass
class Red(Color):
    pass


@dataclass
class Black(Color):
    pass


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
            return T(Black(), t.l, t.k, t.v, t.r)
        else:
            raise Exception("impossible")

    def ins(t: Tree) -> Tree:
        if isinstance(t, E):
            #etna_base miscolor_insert
            return T(Red(), E(), k, v, E())


#etna_mutant miscolor_insert
#            return T(Black(), E(), k, v, E())
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


def balance(col: Color, l: Tree, k: int, v: int, r: Tree) -> Tree:
    match (col, l, k, v, r):
        case (Black(), T(Red(), T(Red(), a, x, xv, b), y, yv, c), z, zv, d):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
        case (Black(), T(Red(), a, x, xv, T(Red(), b, y, yv, c)), z, zv, d):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
        case (Black(), a, x, xv, T(Red(), T(Red(), b, y, yv, c), z, zv, d)):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
        case (Black(), a, x, xv, T(Red(), b, y, yv, T(Red(), c, z, zv, d))):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
        case (_, _, _, _, _):
            return T(col, l, k, v, r)
