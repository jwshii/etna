open Impl
open QCheck

let rec isBST (t : ('a, 'b) tree) : bool =
  let rec every (p : 'a -> bool) (t : ('a, 'b) tree) : bool =
    match t with
    | E -> true
    | T (_, a, x, _, b) -> p x && every p a && every p b
  in
  match t with
  | E -> true
  | T (_, a, x, _, b) ->
      every (( > ) x) a && every (( < ) x) b && isBST a && isBST b

let rec noRedRed (t : ('a, 'b) tree) : bool =
  let blackRoot (t : ('a, 'b) tree) : bool =
    match t with T (R, _, _, _, _) -> false | _ -> true
  in
  match t with
  | E -> true
  | T (B, a, _, _, b) -> noRedRed a && noRedRed b
  | T (R, a, _, _, b) -> blackRoot a && blackRoot b && noRedRed a && noRedRed b

let consistentBlackHeight (t : ('a, 'b) tree) : bool =
  let rec go (t : ('a, 'b) tree) : bool * int =
    match t with
    | E -> (true, 1)
    | T (rb, a, _, _, b) ->
        let aBool, aHeight = go a in
        let bBool, bHeight = go b in
        let isBlack (rb : color) : int = match rb with B -> 1 | R -> 0 in
        (aBool && bBool && aHeight = bHeight, aHeight + isBlack rb)
  in
  fst (go t)

let isRBT (t : ('a, 'b) tree) : bool =
  isBST t && consistentBlackHeight t && noRedRed t

let rec toList (t : ('a, 'b) tree) : ('a * 'b) list =
  match t with E -> [] | T (_, l, k, v, r) -> toList l @ [ (k, v) ] @ toList r

(* -- Validity properties. *)

let prop_InsertValid (t : ('a, 'b) tree) (k : 'a) (v : 'b) =
  assume (isRBT t);
  isRBT (insert k v t)

let prop_DeleteValid (t : ('a, 'b) tree) (k : 'a) =
  assume (isRBT t);
  delete k t >>= fun t' -> Some (isRBT t')

(* ---------- *)

let prop_InsertPost (t : ('a, 'b) tree) (k : 'a) (k' : 'a) (v : 'b) : bool =
  assume (isRBT t);
  let v' = find k' (insert k v t) in
  if k = k' then v' = Some v else v' = find k' t

let prop_DeletePost (t : ('a, 'b) tree) (k : 'a) (k' : 'a) : bool =
  assume (isRBT t);
  delete k t >>= (fun t' -> find k' t') = if k = k' then None else find k' t

(* ---------- *)

(* -- Model-based properties. *)

let deleteKey (k : 'a) (l : ('a * 'b) list) : ('a * 'b) list =
  let rec filter f l =
    match l with
    | [] -> []
    | x :: xs -> if f x then x :: filter f xs else filter f xs
  in
  filter (fun x -> not (fst x = k)) l

let rec l_insert (kv : 'a * 'b) (l : ('a * 'b) list) : ('a * 'b) list =
  match l with
  | [] -> [ kv ]
  | (k, v) :: xs ->
      if fst kv = k then kv :: xs
      else if fst kv < k then kv :: l
      else (k, v) :: l_insert kv xs

let prop_InsertModel (t : ('a, 'b) tree) (k : 'a) (v : 'b) =
  assume (isRBT t);
  toList (insert k v t) = l_insert (k, v) (deleteKey k (toList t))

let prop_DeleteModel (t : ('a, 'b) tree) (k : 'a) =
  assume (isRBT t);
  delete k t >>= fun t' -> Some (toList t' = deleteKey k (toList t))

(* ---------- *)

(* -- Metamorphic properties. *)

let prop_InsertInsert (t : ('a, 'b) tree) (k : 'a) (k' : 'a) (v : 'b) (v' : 'b)
    : bool =
  assume (isRBT t);
  toList (insert k v (insert k' v' t))
  = toList (if k = k' then insert k v t else insert k' v' (insert k v t))

let prop_InsertDelete (t : ('a, 'b) tree) (k : 'a) (k' : 'a) (v : 'b) :
    bool option =
  assume (isRBT t);
  delete k' t >>= fun t' ->
  delete k' (insert k v t) >>= fun t'' ->
  Some (toList (insert k v t') = toList (if k = k' then insert k v t else t''))

let prop_DeleteInsert (t : ('a, 'b) tree) (k : 'a) (k' : 'a) (v' : 'b) =
  assume (isRBT t);
  delete k (insert k' v' t) >>= fun t' ->
  delete k t >>= fun t'' ->
  let t''' = insert k' v' t'' in
  Some (toList t' = toList (if k = k' then t'' else t'''))

let prop_DeleteDelete (t : ('a, 'b) tree) (k : 'a) (k' : 'a) =
  assume (isRBT t);
  delete k' t >>= fun t' ->
  delete k t' >>= fun t'' ->
  delete k t >>= fun t1' ->
  delete k' t1' >>= fun t1'' -> Some (toList t'' = toList t1'')

(* ---------- *)

let sizeRBT (t : ('a, 'b) tree) : int =
  let rec length l = match l with [] -> 0 | _ :: xs -> 1 + length xs in
  length (toList t)
