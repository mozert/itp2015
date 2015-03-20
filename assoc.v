(** remove printing ~ *)
(** printing ~ %\ensuremath{\sim}% *)

(** * Maclane Associative Coherence *)

Require Import coherence.
Require Import coherence2.

Infix "/\0" := (up_0) (at level 59, right associativity).
Print objects.

Infix "~a" := same_assoc (at level 69).
Print same_assoc. (*this print include almost[objects] *)

Infix "~s" := same' (at level 69).
About same'.

Print normal.
Print normalize_aux.
Print normalize.

Print developed.
(* This [development] or factorization lemma necessitate some deep ('well-founded') induction,
using some measure [coherence.length] which shows that this may be related to
arithmetic factorization
*)
Print coherence.length.
About development.

(*
Print developed_normal.
Print developed_normalize.*)

(* begin courtesy cleanup *)
Notation normalize_aux_unitrefl := normalize_aux_arrow.
Notation normalize_unitrefl := normalize_arrow.
(* end courtesy cleanup *)

Notation normalize_aux_unitrefl_assoc := normalize_aux_arrow_assoc.
Print normalize_aux_unitrefl_assoc.
Notation normalize_unitrefl_assoc := normalize_arrow_assoc.
Print normalize_unitrefl_assoc.

Print th360.

Print normalize_aux_map_assoc.


(** * Dosen Semiassociative Coherence *)


Print nodes.

(** [[
Inductive nodes : objects -> Set :=
    self : forall A : objects, A
  | at_left : forall A : objects, A -> forall B : objects, A /\0 B
  | at_right : forall A B : objects, B -> A /\0 B
]]
 *)

Infix "<r" := lt_right (at level 70). 
Print lt_right.

(** [[
Inductive lt_right : forall A : objects, A -> A -> Set :=
    lt_right_cons1 : forall (B : objects) (z : B) (C : objects),
                     self (C /\0 B) <r at_right C z
  | lt_right_cons2 : forall (B C : objects) (x y : B),
                     x <r y -> at_left x C <r at_left y C
  | lt_right_cons3 : forall (B C : objects) (x y : B),
                     x <r y -> at_right C x <r at_right C y
]]
 *)

