from abc import ABC
from dataclasses import dataclass
from typing import Optional, Tuple


class Ty(ABC):
    pass


@dataclass
class TInt(Ty):
    pass


@dataclass
class TBool(Ty):
    pass


class Expr(ABC):
    pass


@dataclass
class Var(Expr):
    name: str


@dataclass
class Int(Expr):
    value: int


@dataclass
class Add(Expr):
    left: Expr
    right: Expr


@dataclass
class Mul(Expr):
    left: Expr
    right: Expr


@dataclass
class Bool(Expr):
    value: bool


@dataclass
class LessThan(Expr):
    left: Expr
    right: Expr


@dataclass
class And(Expr):
    left: Expr
    right: Expr


class Value(ABC):
    pass


@dataclass
class VInt(Value):
    value: int


@dataclass
class VBool(Value):
    value: bool


class Program:
    assignments: list[Tuple[str, Expr]]
    result: Expr

    def __init__(self, assignments: list[Tuple[str, Expr]], result: Expr):
        self.assignments = assignments
        self.result = result

    def __repr__(self):
        assignments = "\n".join(f"{name} = {to_python_expr(expr)}" for name, expr in self.assignments)
        return f"\n<START>\n{assignments}\n{to_python_expr(self.result)}\n<END>"

def infer_type_expr(e: Expr, env: dict[str, Ty]) -> Optional[Ty]:
    match e:
        case Var(name):
            return env.get(name)
        case Int(_):
            return TInt()
        case Add(left, right):
            match (infer_type_expr(left, env), infer_type_expr(right, env)):
                case (TInt(), TInt()):
                    return TInt()
                case _:
                    return None
        case Mul(left, right):
            match (infer_type_expr(left, env), infer_type_expr(right, env)):
                case (TInt(), TInt()):
                    return TInt()
                case _:
                    return None
        case Bool(_):
            return TBool()
        case LessThan(left, right):
            match (infer_type_expr(left, env), infer_type_expr(right, env)):
                case (TInt(), TInt()):
                    return TBool()
                case _:
                    return None
        case And(left, right):
            match (infer_type_expr(left, env), infer_type_expr(right, env)):
                case (TBool(), TBool()):
                    return TBool()
                case _:
                    return None

def infer_type(e: Program) -> Optional[Ty]:
    env = {}
    for name, expr in e.assignments:
        ty = infer_type_expr(expr, env)
        if ty is None:
            return None
        env[name] = ty
    return infer_type_expr(e.result, env)

def evaluate_expr(e: Expr, env: dict[str, Value]) -> Optional[Value]:
    match e:
        case Var(name):
            return env.get(name)
        case Int(value):
            return VInt(value)
        case Add(left, right):
            match (evaluate_expr(left, env), evaluate_expr(right, env)):
                case (VInt(l), VInt(r)):
                    #etna_base add_to_sub
                    return VInt(l + r)
                    #etna_mutant add_to_sub
                    #return VInt(l - r)
                    #etna_mutant_end add_to_sub
                case _:
                    return None
        case Mul(left, right):
            match (evaluate_expr(left, env), evaluate_expr(right, env)):
                case (VInt(l), VInt(r)):
                    return VInt(l * r)
                case _:
                    return None
        case Bool(value):
            return VBool(value)
        case LessThan(left, right):
            match (evaluate_expr(left, env), evaluate_expr(right, env)):
                case (VInt(l), VInt(r)):
                    return VBool(l < r)
                case _:
                    return None
        case And(left, right):
            match (evaluate_expr(left, env), evaluate_expr(right, env)):
                case (VBool(l), VBool(r)):
                    return VBool(l and r)
                case _:
                    return None

def evaluate(p: Program) -> Optional[Value]:
    env = {}
    for name, expr in p.assignments:
        value = evaluate_expr(expr, env)
        if value is None:
            return None
        #etna_base forget_update_env
        env[name] = value
        #etna_mutant forget_update_env
        #etna_mutant_end forget_update_env
    return evaluate_expr(p.result, env)

def to_python_expr(e: Expr) -> str:
    match e:
        case Var(name):
            return name
        case Int(value):
            return str(value)
        case Add(left, right):
            return f"({to_python_expr(left)} + {to_python_expr(right)})"
        case Mul(left, right):
            return f"({to_python_expr(left)} * {to_python_expr(right)})"
        case Bool(value):
            return str(value)
        case LessThan(left, right):
            return f"({to_python_expr(left)} < {to_python_expr(right)})"
        case And(left, right):
            return f"({to_python_expr(left)} and {to_python_expr(right)})"
        case e:
            print(e)
            raise Exception("impossible")

def python_evaluate(p: Program):
    assignments = "\n".join(f"{name} = {to_python_expr(expr)}" for name, expr in p.assignments)
    l = {}
    g = {}
    exec(assignments, l, g)
    return eval(to_python_expr(p.result), l, g)

def variable_uses(p: Program) -> int:
    def variable_uses_expr(e: Expr):
        match e:
            case Var(_):
                return 1
            case Int(_):
                return 0
            case Bool(_):
                return 0
            case Add(left, right):
                return variable_uses_expr(left) + variable_uses_expr(right)
            case Mul(left, right):
                return variable_uses_expr(left) + variable_uses_expr(right)
            case LessThan(left, right):
                return variable_uses_expr(left) + variable_uses_expr(right)
            case And(left, right):
                return variable_uses_expr(left) + variable_uses_expr(right)
            case e:
                print(e)
                raise Exception("impossible")

    return sum(variable_uses_expr(expr) for _, expr in p.assignments) + variable_uses_expr(p.result)