open Impl
open QCheck

let mt (e : expr) : typ option = getTyp [] e

let isSome (a : 'a option) : bool =
  match a with Some _ -> true | None -> false

let mtypeCheck (e : expr option) (t : typ) : bool =
  match e with Some e' -> typeCheck [] e' t | None -> true

let prop_SinglePreserve (e : expr) : bool option =
  assume (isSome (mt e));
  mt e >>= fun t' -> Some (mtypeCheck (pstep e) t')

let prop_MultiPreserve (e : expr) : bool option =
  assume (isSome (mt e));
  mt e >>= fun t' -> Some (mtypeCheck (multistep 40 pstep e) t')

let rec sizeSTLC (e : expr) : int =
  match e with
  | Abs (_, e) -> 1 + sizeSTLC e
  | App (e1, e2) -> 1 + sizeSTLC e1 + sizeSTLC e2
  | _ -> 1
