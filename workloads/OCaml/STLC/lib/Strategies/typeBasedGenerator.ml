open Impl
open Spec
open QCheck

(* --------------------- Generator --------------------- *)

let tfun a b = TFun (a, b)

let typGen =
  let open QCheck.Gen in
  let rec _typGen n =
    if n <= 0 then return TBool
    else oneof [ map2 tfun (_typGen (n / 2)) (_typGen (n / 2)); return TBool ]
  in
  sized _typGen

let e_var v = Var v
let e_bool b = Bool b
let e_abs t e = Abs (t, e)
let e_app e e' = App (e, e')

let typebased =
  let open QCheck.Gen in
  let rec _exprGen n =
    if n <= 0 then oneof [ map e_var nat; map e_bool bool ]
    else
      oneof
        [
          map2 e_abs typGen (_exprGen (n / 2));
          map2 e_app (_exprGen (n / 2)) (_exprGen (n / 2));
        ]
  in
  sized (fun n -> _exprGen n)

let var_to_string n =
  String.make 1 (String.get "abcdefghijklmnopqrstuvwxyz" (n mod 26))

let rec print_typ t =
  match t with
  | TBool -> "Bool"
  | TFun (t, t') -> "(" ^ print_typ t ^ "->" ^ print_typ t' ^ ")"

  (* i think this is wrong *)
let print_expr e =
  let rec _print_expr n e =
    match e with
    | Var n -> var_to_string n
    | Bool b -> string_of_bool b
    | Abs (t, e') ->
        "\\" ^ var_to_string n ^ ":" ^ print_typ t ^ ","
        ^ _print_expr (1 + n) e'
    | App (e1, e2) -> _print_expr n e1 ^ " " ^ _print_expr n e2
  in
  _print_expr 0 e

let makeTest name = Test.make ~count:1000 ~name
let arbitrary_of_gen g = make g ~print:print_expr

(* --------------------- Tests --------------------- *)

let ( ~~ ) x = match x with Some false -> false | _ -> true

let test_prop_SinglePreserve aExpr =
  makeTest "test_prop_SinglePreserve" aExpr (fun e -> ~~(prop_SinglePreserve e))

(*! QuickChick test_prop_SinglePreserve. *)

let test_prop_MultiPreserve aExpr =
  makeTest "test_prop_MultiPreserve" aExpr (fun e -> ~~(prop_MultiPreserve e))

(*! QuickChick test_prop_MultiPreserve. *)