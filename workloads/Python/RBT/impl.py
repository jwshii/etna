from __future__ import annotations
from abc import ABC
from dataclasses import dataclass
from typing import Optional, Tuple


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

def lookup(t: Tree, k: int) -> Optional[int]:
    if isinstance(t, E):
        return None
    elif isinstance(t, T):
        if k < t.k:
            return lookup(t.l, k)
        elif k > t.k:
            return lookup(t.r, k)
        else:
            return t.v
    else:
        raise Exception("impossible")


def insert(k: int, v: int, t: Tree) -> Tree:

    def ins(t: Tree) -> Tree:
        if isinstance(t, E):
            #etna_base miscolor_insert
            return T(Red(), E(), k, v, E())


#etna_mutant miscolor_insert
#            return T(Black(), E(), k, v, E())
#etna_mutant_end miscolor_insert
        elif isinstance(t, T):
            #etna_base insert_1
            #etna_base insert_2
            #etna_base insert_3
            #etna_base no_balance_insert_1
            #etna_base no_balance_insert_2
            if k < t.k:
                return balance(t.c, ins(t.l), t.k, t.v, t.r)
            elif k > t.k:
                return balance(t.c, t.l, t.k, t.v, ins(t.r))
            return T(t.c, t.l, k, v, t.r)
#etna_mutant insert_1
#            return T(t.c, t.l, k, v, t.r)
#etna_mutant_end insert_1
#etna_mutant insert_2
#            if k < t.k:
#                return balance(t.c, ins(t.l), t.k, t.v, t.r)
#            return T(t.c, t.l, k, v, t.r)
#etna_mutant_end insert_2
#etna_mutant insert_3
#            if k < t.k:
#                return balance(t.c, ins(t.l), t.k, t.v, t.r)
#            elif k > t.k:
#                return balance(t.c, t.l, t.k, t.v, ins(t.r))
#            return T(t.c, t.l, t.k, t.v, t.r)
#etna_mutant_end insert_3
#etna_mutant no_balance_insert_1
#            if k < t.k:
#                return T(t.c, ins(t.l), t.k, t.v, t.r)
#            elif k > t.k:
#                return balance(t.c, t.l, t.k, t.v, ins(t.r))
#            return T(t.c, t.l, k, v, t.r)
#etna_mutant_end no_balance_insert_1
#etna_mutant no_balance_insert_2
#            if k < t.k:
#                return balance(t.c, ins(t.l), t.k, t.v, t.r)
#            elif k > t.k:
#                return T(t.c, t.l, t.k, t.v, ins(t.r))
#            return T(t.c, t.l, k, v, t.r)
#etna_mutant_end no_balance_insert_2
        else:
            raise Exception("impossible")

    return blacken(ins(t))

def blacken(t: Tree) -> Tree:
    if isinstance(t, E):
        return t
    elif isinstance(t, T):
        return T(Black(), t.l, t.k, t.v, t.r)
    else:
        raise Exception("impossible")

def redden(t: Tree) -> Tree:
    if isinstance(t, E):
        return t
    elif isinstance(t, T):
        return T(Red(), t.l, t.k, t.v, t.r)
    else:
        raise Exception("impossible")

def bal_left(l: Tree, k: int, v: int, r: Tree) -> Tree:
    match (l, k, v, r):
        case (T(Red(), a, x, xv, b), y, yv, c):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, c)
        case (bl, x, vx, T(Black(), a, y, vy, b)):
            return balance(Black(), bl, x, vx, T(Red(), a, y, vy, b))
        case (bl, x, vx, T(Red(), T(Black(), a, y, vy, b), z, vz, c)):
            return T(Red(), T(Black(), bl, x, vx, a), y, vy, balance(Black(), b, z, vz, redden(c)))
        case (_, _, _, _):
            return T(Black(), l, k, v, r)

def bal_right(l: Tree, k: int, v: int, r: Tree) -> Tree:
    match (l, k, v, r):
        case (a, x, xv, T(Red(), b, y, yv, c)):
            return T(Red(), a, x, xv, T(Black(), b, y, yv, c))
        case (T(Black(), a, x, xv, b), y, yv, bl):
            return balance(Black(), T(Red(), a, x, xv, b), y, yv, bl)
        case (T(Red(), a, x, xv, T(Black(), b, y, yv, c)), z, zv, bl):
            return T(Red(), balance(Black(), redden(a), x, xv, b), y, yv, T(Black(), c, z, zv, bl))
        case (_, _, _, _):
            return T(Black(), l, k, v, r)


def balance(col: Color, l: Tree, k: int, v: int, r: Tree) -> Tree:
    match (col, l, k, v, r):
        case (Black(), T(Red(), T(Red(), a, x, xv, b), y, yv, c), z, zv, d):
        #etna_base swap_cd
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
#etna_mutant swap_cd
#            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), d, z, zv, c))
#etna_mutant_end swap_cd
        case (Black(), T(Red(), a, x, xv, T(Red(), b, y, yv, c)), z, zv, d):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
        case (Black(), a, x, xv, T(Red(), T(Red(), b, y, yv, c), z, zv, d)):
            #etna_base swap_bc
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
#etna_mutant swap_bc
#            return T(Red(), T(Black(), a, x, xv, c), z, zv, T(Black(), b, y, yv, d))
#etna_mutant_end swap_bc
        case (Black(), a, x, xv, T(Red(), b, y, yv, T(Red(), c, z, zv, d))):
            return T(Red(), T(Black(), a, x, xv, b), y, yv, T(Black(), c, z, zv, d))
        case (_, _, _, _, _):
            return T(col, l, k, v, r)

def join(l: Tree, r: Tree) -> Tree:
    match (l, r):
        case (E(), _):
            return r
        case (_, E()):
            return l
        case (T(Red(), a, x, vx, b), T(Red(), c, y, vy, d)):
            new_t = join(b, c)
            match new_t:
                case T(Red(), new_b, z, vz, new_c):
                    return T(Red(), T(Red(), a, x, vx, new_b), z, vz, T(Red(), new_c, y, vy, d))
                case bc:
                    return T(Red(), a, x, vx, T(Red(), bc, y, vy, d))
        case (T(Black(), a, x, vx, b), T(Black(), c, y, vy, d)):
            new_t = join(b, c)
            match new_t:
                case T(Red(), new_b, z, vz, new_c):
                    return T(Red(), T(Black(), a, x, vx, new_b), z, vz, T(Black(), new_c, y, vy, d))
                case bc:
                    return bal_left(a, x, vx, T(Black(), bc, y, vy, d))
        case (a, T(Red(), b, x, vx, c)):
            return T(Red(), join(a, b), x, vx, c)
        case (T(Red(), a, x, vx, b), c):
            return T(Red(), a, x, vx, join(b, c))
        case _:
            raise Exception("impossible")

def delete(k: int, t: Tree) -> Tree:

    def aux_left(l: Tree, k: int, v: int, r: Tree) -> Tree:
        new_l = aux(l)
        if isinstance(l, T) and l.c.is_black():
            return bal_left(new_l, k, v, r)
        else:
            return T(Red(), new_l, k, v, r)

    def aux_right(l: Tree, k: int, v: int, r: Tree) -> Tree:
        new_r = aux(r)
        if isinstance(r, T) and r.c.is_black():
            return bal_right(l, k, v, new_r)
        else:
            return T(Red(), l, k, v, new_r)

    def aux(t: Tree) -> Tree:
        if isinstance(t, E):
            return t
        elif isinstance(t, T):
            if k < t.k:
                return aux_left(t.l, t.k, t.v, t.r)
            elif k > t.k:
                return aux_right(t.l, t.k, t.v, t.r)
            else:
                return join(t.l, t.r)
        else:
            raise Exception("impossible")

    return blacken(aux(t))