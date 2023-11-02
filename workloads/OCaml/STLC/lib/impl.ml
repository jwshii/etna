open List
open Option

let ( >>= ) = bind

type typ = TBool | TFun of typ * typ
type expr = Var of int | Bool of bool | Abs of typ * expr | App of expr * expr
type ctx = typ list

let rec getTyp (c : ctx) (e : expr) : typ option =
  match e with
  | Var n -> nth_opt c n
  | Bool _ -> Some TBool
  | Abs (t, e) -> getTyp (t :: c) e >>= fun t' -> Some (TFun (t, t'))
  | App (e1, e2) -> (
      getTyp c e1 >>= fun t' ->
      match t' with
      | TFun (t11, t12) ->
          getTyp c e2 >>= fun t2 -> if t11 = t2 then Some t12 else None
      | _ -> None)

let typeCheck (c : ctx) (e : expr) (t : typ) : bool =
  match getTyp c e with Some t' -> t = t' | None -> false

let shift (d : int) (ex : expr) : expr = let _ = ignore (d, ex) in
  let rec go (c : int) (e : expr) =
    match e with
    | Var n ->
        (*! *)
        if n < c then Var n
        else Var (n + d)
          (*!! shift_var_none *)
          (*!
            Var n
          *)
          (*!! shift_var_all *)
          (*!
            Var (n + d)
          *)
          (*!! shift_var_leq *)
          (*!
            if n <= c then Var n
            else Var (n + d)
          *)
    | Bool b -> Bool b
    | Abs (t, e) ->
        (*! *)
        Abs (t, go (1 + c) e)
        (*!! shift_abs_no_incr *)
        (*!
          Abs (t, go c e)
        *)
    | App (e1, e2) -> App (go c e1, go c e2)
  in
  go 0 ex

let rec subst (n : int) (s : expr) (e : expr) : expr =
  match (n, s, e) with
  | n, s, Var m ->
      let () = ignore (n, s, m) in
      (*! *)
      if m = n then s else Var m
      (*!! subst_var_all *)
      (*!
        s
      *)
      (*!! subst_var_none *)
      (*!
        Var m
      *)
  | _, _, Bool b -> Bool b
  | n, s, Abs (t, e) ->
      (*! *)
      Abs (t, subst (n + 1) (shift 1 s) e)
      (*!! subst_abs_no_shift *)
      (*!
        Abs (t, subst (n + 1) s e)
      *)
      (*!! subst_abs_no_incr *)
      (*!
        Abs (t, subst n (shift 1 s) e)
      *)
  | n, s, App (e1, e2) -> App (subst n s e1, subst n s e2)

let substTop (s : expr) (e : expr) : expr =
  (*! *)
  shift (-1) (subst 0 (shift 1 s) e)
(*!! substTop_no_shift *)
(*!
  subst 0 s e
*)
(*!! substTop_no_shift_back *)
(*!
  subst 0 (shift 1 s) e
*)

let fromOption a a' = match a' with Some v -> v | None -> a

let rec pstep (e : expr) : expr option =
  match e with
  | Abs (t, e) -> pstep e >>= fun e' -> Some (Abs (t, e'))
  | App (Abs (_, e1), e2) ->
      let e1' = fromOption e1 (pstep e1) in
      let e2' = fromOption e2 (pstep e2) in
      Some (substTop e2' e1')
  | App (e1, e2) -> (
      match (pstep e1, pstep e2) with
      | None, None -> None
      | me1, me2 ->
          let e1' = fromOption e1 me1 in
          let e2' = fromOption e2 me2 in
          Some (App (e1', e2')))
  | _ -> None

let rec multistep (f : int) (step : expr -> expr option) (e : expr) :
    expr option =
  match f with
  | 0 -> None
  | f -> (
      let f' = f - 1 in
      match step e with None -> Some e | Some e' -> multistep f' step e')

let rec isNF (e : expr) : bool =
  match e with
  | Var _ -> true
  | Bool _ -> true
  | Abs (_, e) -> isNF e
  | App (Abs (_, _), _) -> false
  | App (e1, e2) -> isNF e1 && isNF e2
