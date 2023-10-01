open QCheck
open Impl
open List

type kvlist = (int * int) list

let rec keys (t: tree): int list =
  match t with
  | E -> []
  | T (l, k, _v, r) ->
    let lk = keys l in
    let rk = keys r in
    [k] @ lk @ rk

let rec all (f: 'a -> bool) (l: 'a list): bool =
  match l with
  | [] -> true
  | x::xs -> f x && all f xs


let rec isBST (t: tree) : bool =
  match t with
  | E -> true
  | T (l, k, _, r) ->
    isBST l
    && isBST r
    && all (fun k' -> k' < k) (keys l)
    && all (fun k' -> k' > k) (keys r)

let rec toList (t: tree) : kvlist =
  match t with
  | E -> []
  | T (l, k, v, r) ->
    toList l @ [(k, v)] @ toList r


(* -- Validity Properties. *)

let prop_InsertValid : (tree * int * int) -> bool =
  fun (t, k, v)->
    assume (isBST t);
    isBST (insert k v t)

let prop_DeleteValid : (tree * int) -> bool =
  fun (t, k) ->
    assume (isBST t);
    isBST (delete k t)

let prop_UnionValid : (tree * tree) -> bool =
  fun (t, t')->
    assume (isBST t);
    assume (isBST t');
    isBST (union t t')

(* ---------- *)

(* -- Postcondition Properties. *)

let prop_InsertPost : (tree * int * int * int) -> bool =
  fun (t, k, k', v) ->
    assume (isBST t);
    Impl.find k' (insert k v t) = (if k = k' then Some v else Impl.find k' t)

let prop_DeletePost : (tree * int * int) -> bool =
  fun (t, k, k') ->
    Impl.find k' (delete k t) = (if k = k' then None else Impl.find k' t)


let prop_UnionPost : (tree * tree * int) -> bool =
  fun (t, t', k) ->
    let lhs  = Impl.find k (union t t') in
    let rhs  = Impl.find k t in
    let rhs' = Impl.find k t' in
    (lhs = rhs || lhs = rhs')

(* ---------- *)

(* -- Model-based properties. *)

let deleteKey (k: int) (l: kvlist): kvlist =
  filter (fun (x, _) -> x = k) l


let rec l_insert ((k, v): int * int) (l: kvlist) : kvlist =
  match l with
  | [] -> [(k, v)]
  | (k', v')::xs ->
    if k = k' then (k, v)::xs
    else if k < k' then (k, v)::l
    else (k', v')::(l_insert (k, v) xs)

let rec sorted (l: kvlist) : bool =
  match l with
  | [] -> true
  | (k, _v)::l' ->
    match l' with
    | [] -> true
    | (k', _v')::_l'' ->
      (k < k') && sorted l'

let prop_InsertModel : (tree * int * int) -> bool =
  fun (t, k, v) ->
    assume (isBST t);
    toList (insert k v t) = l_insert (k, v) (deleteKey k (toList t))

let prop_DeleteModel : (tree * int) -> bool =
  fun (t, k) ->
    assume (isBST t);
    toList (delete k t) = deleteKey k (toList t)

let rec l_sort (l: kvlist) : kvlist =
  match l with
  | [] -> []
  | (k, v)::l' ->
    l_insert (k, v) (l_sort l')

let l_find (k: int) (l: kvlist): int option =
  match filter (fun (x, _) -> x = k) l with
  | [] -> None
  | (_, v)::_ -> Some v

let rec l_unionBy (f: int -> int -> int) (l1: kvlist) (l2: kvlist) : kvlist =
  match l1 with
  | [] -> l2
  | (k, v)::l1' ->
    let l2' = deleteKey k l2 in
    let v' = match l_find k l2 with
             | None -> v
             | Some v' -> f v v' in
    l_insert (k, v') (l_unionBy f l1' l2')

let prop_UnionModel : (tree * tree) -> bool =
  fun (t, t') ->
    assume (isBST t);
    assume (isBST t');
    toList (union t t') = l_sort (l_unionBy (fun x _ -> x) (toList t) (toList t'))

(* ---------- *)

let treeEq (t: tree) (t': tree) =
  toList t = toList t'

let (=|=) = treeEq

(* -- Metamorphic properties. *)


let prop_InsertInsert : (tree * int * int * int * int) -> bool =
  fun (t, k, k', v, v') ->
    assume (isBST t);
    insert k v (insert k' v' t) =|= if k = k' then insert k v t else insert k' v' (insert k v t)

let prop_InsertDelete : (tree * int * int * int) -> bool =
  fun (t, k, k', v) ->
    assume (isBST t);
    insert k v (delete k' t) =|= if k = k' then insert k v t else delete k' (insert k v t)

let prop_InsertUnion : (tree * tree * int * int) -> bool =
  fun (t, t', k, v) ->
    assume (isBST t);
    assume (isBST t');
    insert k v (union t t') =|= union (insert k v t) t'

let prop_DeleteInsert : (tree * int * int * int) -> bool =
  fun (t, k, k', v') ->
    assume (isBST t);
    delete k (insert k' v' t) =|= if k = k' then delete k t else insert k' v' (delete k t)

let prop_DeleteDelete : (tree * int * int) -> bool =
  fun (t, k, k') ->
  assume (isBST t);
  delete k (delete k' t) =|= delete k' (delete k t)

let prop_DeleteUnion : (tree * tree * int) -> bool  =
  fun (t, t', k) ->
    assume (isBST t);
    assume (isBST t');
    delete k (union t t')  =|= union (delete k t) (delete k t')

let prop_UnionDeleteInsert : (tree * tree * int * int) -> bool =
  fun (t, t', k, v) ->
    assume (isBST t);
    assume (isBST t');
    union (delete k t) (insert k v t') =|= insert k v (union t t')

let prop_UnionUnionIdem : tree -> bool =
  fun t ->
  assume (isBST t);
  union t t =|= t

let prop_UnionUnionAssoc : (tree * tree * tree) -> bool =
  fun (t1, t2, t3) ->
  assume (isBST t1);
  assume (isBST t2);
  assume (isBST t3);
  union (union t1 t2) t3 =|= union t1 (union t2 t3)


(* ---------- *)

let sizeBST (t: tree) : int =
  length (toList t)

(* -- Size properties. *)

