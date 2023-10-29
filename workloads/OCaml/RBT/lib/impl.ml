open Option

let ( >>= ) = bind

type color = R | B
type ('a, 'b) tree = E | T of color * ('a, 'b) tree * 'a * 'b * ('a, 'b) tree

let fuel = 100000

let blacken (t : ('a, 'b) tree) : ('a, 'b) tree =
  match t with E -> E | T (_, l, k, v, r) -> T (B, l, k, v, r)

let redden (t : ('a, 'b) tree) : ('a, 'b) tree option =
  match t with T (B, l, k, v, r) -> Some (T (R, l, k, v, r)) | _ -> None

let balance (col : color) (tl : ('a, 'b) tree) (k : 'a) (v : 'b)
    (tr : ('a, 'b) tree) : ('a, 'b) tree =
  match (col, tl, k, v, tr) with
  (*! *)
  | B, T (R, T (R, a, x, vx, b), y, vy, c), z, vz, d ->
      T (R, T (B, a, x, vx, b), y, vy, T (B, c, z, vz, d))
  (*!! swap_ad *)
  (*!
      | B, T (R, T (R, a, x, vx, b), y, vy, c), z, vz, d -> T (R, T (B, a, x, vx, b), y, vy, T (B, d, z, vz, c))
  *)
  | B, T (R, a, x, vx, T (R, b, y, vy, c)), z, vz, d ->
      T (R, T (B, a, x, vx, b), y, vy, T (B, c, z, vz, d))
  (*! *)
  | B, a, x, vx, T (R, T (R, b, y, vy, c), z, vz, d) ->
      T (R, T (B, a, x, vx, b), y, vy, T (B, c, z, vz, d))
  (*!! swap_bc *)
  (*!
      | B, a, x, vx, T (R, T (R, b, y, vy, c), z, vz, d) -> T (R, T (B, a, x, vx, c), y, vy, T (B, b, z, vz, d))
  *)
  | B, a, x, vx, T (R, b, y, vy, T (R, c, z, vz, d)) ->
      T (R, T (B, a, x, vx, b), y, vy, T (B, c, z, vz, d))
  | rb, a, x, vx, b -> T (rb, a, x, vx, b)

let rec insert (k : 'a) (v : 'b) (t : ('a, 'b) tree) : ('a, 'b) tree =
  let _ = ignore insert in
  let rec ins (x : 'a) (vx : 'b) (s : ('a, 'b) tree) : ('a, 'b) tree =
    match (x, vx, s) with
    | x, vx, E ->
        (*! *)
        T (R, E, x, vx, E)
    (*!! miscolor_insert *)
    (*!
      T (B, E, x, vx, E)
    *)
    | x, vx, T (rb, a, y, vy, b) -> let _ = ignore (rb, a, y, vy, b, ins) in
        (*! *)
        if x < y then balance rb (ins x vx a) y vy b
        else if y < x then balance rb a y vy (ins x vx b)
        else T (rb, a, y, vx, b)
    (*!! insert_1 *)
    (*!
      T (R, E, x, vx, E)
    *)
    (*!! insert_2 *)
    (*!
      if x < y then balance rb (ins x vx a) y vy b
      else T (rb, a, y, vx, b)
    *)
    (*!! insert_3 *)
    (*!
      if x < y then balance rb (ins x vx a) y vy b
      else if y < x then balance rb a y vy (ins x vx b)
      else T (rb, a, y, vy, b)
    *)
    (*!! no_balance_insert_1 *)
    (*!
      if x < y then T (rb, ins x vx a, y, vy, b)
      else if y < x then balance rb a y vy (ins x vx b)
      else T (rb, a, y, vx, b)
    *)
    (*!! no_balance_insert_2 *)
    (*!
      if x < y then balance rb (ins x vx a) y vy b
      else if y < x then T (rb, a, y, vy, insert x vx b)
      else T (rb, a, y, vx, b)
    *)
  in

  blacken (ins k v t)

let balLeft (tl : ('a, 'b) tree) (k : 'a) (v : 'b) (tr : ('a, 'b) tree) :
    ('a, 'b) tree option =
  match (tl, k, v, tr) with
  | T (R, a, x, vx, b), y, vy, c -> Some (T (R, T (B, a, x, vx, b), y, vy, c))
  | bl, x, vx, T (B, a, y, vy, b) ->
      Some (balance B bl x vx (T (R, a, y, vy, b)))
  | bl, x, vx, T (R, T (B, a, y, vy, b), z, vz, c) ->
      (*! *)
      redden c >>= fun c' ->
      Some (T (R, T (B, bl, x, vx, a), y, vy, balance B b z vz c'))
  (*!! miscolor_balLeft *)
  (*!
    Some (T (R, T (B, bl, x, vx, a), y, vy, (balance B b z vz c)))
  *)
  | _, _, _, _ -> None

let balRight (tl : ('a, 'b) tree) (k : 'a) (v : 'b) (tr : ('a, 'b) tree) :
    ('a, 'b) tree option =
  match (tl, k, v, tr) with
  | a, x, vx, T (R, b, y, vy, c) -> Some (T (R, a, x, vx, T (B, b, y, vy, c)))
  | T (B, a, x, vx, b), y, vy, bl ->
      Some (balance B (T (R, a, x, vx, b)) y vy bl)
  | T (R, a, x, vx, T (B, b, y, vy, c)), z, vz, bl ->
      (*! *)
      redden a >>= fun a' ->
      Some (T (R, balance B a' x vx b, y, vy, T (B, c, z, vz, bl)))
  (*!! miscolor_balRight *)
  (*!
      Some (T (R, (balance B a x vx b), y, vy, T (B, c, z, vz, bl)))
  *)
  | _, _, _, _ -> None

let rec _join (t1 : ('a, 'b) tree) (t2 : ('a, 'b) tree) (f : int) :
    ('a, 'b) tree option =
  match f with
  | 0 -> None
  | f -> (
      let f' = f - 1 in
      match (t1, t2) with
      | E, a -> Some a
      | a, E -> Some a
      | T (R, a, x, vx, b), T (R, c, y, vy, d) -> (
          match _join b c f' with
          | None -> None
          | Some (T (R, b', z, vz, c')) ->
              (*! *)
              Some (T (R, T (R, a, x, vx, b'), z, vz, T (R, c', y, vy, d)))
          (*!! miscolor_join_1 *)
          (*!
            Some (T (R, T (B, a, x, vx, b'), z, vz, T (B, c', y, vy, d)))
          *)
          | Some bc -> Some (T (R, a, x, vx, T (R, bc, y, vy, d))))
      | T (B, a, x, vx, b), T (B, c, y, vy, d) -> (
          match _join b c f' with
          | None -> None
          | Some (T (R, b', z, vz, c')) ->
              (*! *)
              Some (T (R, T (B, a, x, vx, b'), z, vz, T (B, c', y, vy, d)))
          (*!! miscolor_join_2 *)
          (*!
            Some (T (R, T (R, a, x, vx, b'), z, vz, T (R, c', y, vy, d)))
          *)
          | Some bc -> balLeft a x vx (T (B, bc, y, vy, d)))
      | a, T (R, b, x, vx, c) -> (
          match _join a b f' with
          | None -> None
          | Some t' -> Some (T (R, t', x, vx, c)))
      | T (R, a, x, vx, b), c ->
          _join b c f' >>= fun t' -> Some (T (R, a, x, vx, t')))

let join (t1 : ('a, 'b) tree) (t2 : ('a, 'b) tree) : ('a, 'b) tree option =
  _join t1 t2 fuel

let rec del (x : 'a) (s : ('a, 'b) tree) (f : int) : ('a, 'b) tree option =
  match f with
  | 0 -> None
  | f ->
      let f' = f - 1 in
      match s with
      | E -> Some E
      | T (_, a, y, vy, b) -> let _ = ignore (vy) in
          (*! *)
          if x < y then delLeft x a y vy b f'
          else if y < x then delRight x a y vy b f
          else join a b

(*!! delete_4 *)
(*!
  if x < y then del x a f'
  else if y < x then del x b f'
  else join a b
*)
(*!! delete_5 *)
(*!
  if y < x then delLeft x a y vy b f'
  else if x < y then delRight x a y vy b f'
  else join a b
*)
and delLeft (x : 'a) (dl : ('a, 'b) tree) (dy : 'a) (dvy : 'b)
    (dr : ('a, 'b) tree) (f : int) : ('a, 'b) tree option =
  match f with
  | 0 -> None
  | f -> (
      let f' = f - 1 in
      match (dl, dy, dvy, dr) with
      | T (B, al, ax, avx, ar), y, vy, b ->
          del x (T (B, al, ax, avx, ar)) f' >>= fun t' -> balLeft t' y vy b
      | a, y, vy, b -> del x a f' >>= fun t' -> Some (T (R, t', y, vy, b)))

and delRight (x : 'a) (dl : ('a, 'b) tree) (dy : 'a) (dvy : 'b)
    (dr : ('a, 'b) tree) (f : int) : ('a, 'b) tree option =
  match f with
  | 0 -> None
  | f -> (
      let f' = f - 1 in
      match (dl, dy, dvy, dr) with
      | a, y, vy, T (B, bl, bx, bvx, br) ->
          del x (T (B, bl, bx, bvx, br)) f' >>= fun t' -> balRight a y vy t'
      | a, y, vy, b -> del x b f' >>= fun t' -> Some (T (R, a, y, vy, t')))

let delete (x : 'a) (t : ('a, 'b) tree) : ('a, 'b) tree option =
  (*! *)
  del x t fuel >>= fun t' -> Some (blacken t')
(*!! miscolor_delete *)
(*!
  del x t fuel
*)

let rec find (x : 'a) (t : ('a, 'b) tree) : 'b option =
  match t with
  | E -> None
  | T (_, l, y, vy, r) ->
      if x < y then find x l else if y < x then find x r else Some vy

let rec size (t : ('a, 'b) tree) : int =
  match t with E -> 0 | T (_, l, _, _, r) -> 1 + size l + size r
