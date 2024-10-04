From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.

Variable A : Type.
Variable start : pred A.
Variable ended : pred A.
Variable inv : A -> Prop.
Variable step : A -> option A.

Variable O : Type. (* the power of the observer (e.g. a label) *)
Variable low : O -> pred A.
Variable indist : O -> rel A.

Definition eeni : Prop :=
  forall (o : O) (s1 s2 s1' s2' : A),
    start s1 ->
    start s2 ->
    indist o s1 s2 ->
    rexec s1 s1' ->
    rexec s2 s2' ->
    ended s1' ->
    ended s2' ->
    indist o s1' s2'.