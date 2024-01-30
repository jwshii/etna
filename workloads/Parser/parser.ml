
(* 
EBNF Grammar for Property Definitions

Example:
  Definition test_prop_InsertValid   :=
    forAllMaybe (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10) (fun (t : Tree) =>
    forAll arbitrary (fun (k: nat)  =>
    forAll arbitrary (fun (v: nat) =>
    prop_InsertValid t k v)))
  .


Property ::= "Definition" Name ":=" Generation+ FunctionCall

Generation ::= Qualifier Generator "(fun (" Variable ":" Type ") =>"

FunctionCall ::= "prop_" Name Variable+ ")"+

Qualifier ::= "forAllMaybe" | "forAll"

Generator ::= "arbitrary" | /\(\)

Code ::= [a-zA-Z0-9_ =>]+
*)
