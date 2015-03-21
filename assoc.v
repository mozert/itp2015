(** remove printing ~ *)
(** printing ~ %\ensuremath{\sim}% *)

(** * Maclane Associative Coherence *)

Require Import coherence.
Require Import coherence2.

Set Implicit Arguments.

Infix "/\0" := (up_0) (at level 59, right associativity).
Print objects.
(** [[
Inductive objects : Set :=
    letter : letters -> objects | up_0 : objects -> objects -> objects.
]]
*)

Infix "~a" := same_assoc (at level 69).
Print same_assoc.
(** [[
Inductive same_assoc
              : forall A B : objects,
                arrows_assoc A B -> arrows_assoc A B -> Set :=
    same_assoc_refl : forall (A B : objects) (f : arrows_assoc A B), f ~a f
  | same_assoc_trans : forall (A B : objects) (f g h : arrows_assoc A B),
                       f ~a g -> g ~a h -> f ~a h
  | same_assoc_sym : forall (A B : objects) (f g : arrows_assoc A B),
                     f ~a g -> g ~a f
  | same_assoc_cong_com : forall (A B C : objects) (f f0 : arrows_assoc A B)
                            (g g0 : arrows_assoc B C),
                          f ~a f0 -> g ~a g0 -> g <oa f ~a g0 <oa f0
  | same_assoc_cong_up_1 : forall (A B A0 B0 : objects)
                             (f f0 : arrows_assoc A B)
                             (g g0 : arrows_assoc A0 B0),
                           f ~a f0 -> g ~a g0 -> f /\1a g ~a f0 /\1a g0
  | same_assoc_cat_left : forall (A B : objects) (f : arrows_assoc A B),
                          unitt_assoc B <oa f ~a f
  | same_assoc_cat_right : forall (A B : objects) (f : arrows_assoc A B),
                           f <oa unitt_assoc A ~a f
  | same_assoc_cat_assoc : forall (A B C D : objects) (f : arrows_assoc A B)
                             (g : arrows_assoc B C) (h : arrows_assoc C D),
                           h <oa g <oa f ~a (h <oa g) <oa f
  | same_assoc_bif_up_unit : forall A B : objects,
                             unitt_assoc A /\1a unitt_assoc B ~a
                             unitt_assoc (A /\0 B)
  | same_assoc_bif_up_com : forall (A B C A0 B0 C0 : objects)
                              (f : arrows_assoc A B) (g : arrows_assoc B C)
                              (f0 : arrows_assoc A0 B0)
                              (g0 : arrows_assoc B0 C0),
                            (g <oa f) /\1a (g0 <oa f0) ~a
                            g /\1a g0 <oa f /\1a f0
  | same_assoc_bracket_left_5 : forall A B C D : objects,
                                bracket_left_assoc (A /\0 B) C D <oa
                                bracket_left_assoc A B (C /\0 D) ~a
                                bracket_left_assoc A B C /\1a unitt_assoc D <oa
                                bracket_left_assoc A (B /\0 C) D <oa
                                unitt_assoc A /\1a bracket_left_assoc B C D
  | same_assoc_nat : forall (A A' : objects) (f : arrows_assoc A' A)
                       (B B' : objects) (g : arrows_assoc B' B)
                       (C C' : objects) (h : arrows_assoc C' C),
                     bracket_left_assoc A B C <oa f /\1a g /\1a h ~a
                     (f /\1a g) /\1a h <oa bracket_left_assoc A' B' C'
  | same_assoc_bracket_right_bracket_left : forall A B C : objects,
                                            bracket_right_assoc A B C <oa
                                            bracket_left_assoc A B C ~a
                                            unitt_assoc (A /\0 B /\0 C)
  | same_assoc_bracket_left_bracket_right : forall A B C : objects,
                                            bracket_left_assoc A B C <oa
                                            bracket_right_assoc A B C ~a
                                            unitt_assoc ((A /\0 B) /\0 C)
]]
*)

Infix "~s" := same' (at level 69).
About same'.

Print normal.
(** [[
Inductive normal : objects -> Set :=
    normal_cons1 : forall l : letters, normal (letter l)
  | normal_cons2 : forall (A : objects) (l : letters),
                   normal A -> normal (A /\0 letter l).
]]
*)
Print normalize_aux.
(** [[
fix normalize_aux (Z A : objects) {struct A} : objects :=
  match A with
  | letter l => Z /\0 letter l
  | A1 /\0 A2 => normalize_aux (normalize_aux Z A1) A2
  end
     : objects -> objects -> objects
]]
*)
Print normalize.
(** [[
fix normalize (A : objects) : objects :=
  match A with
  | letter l => letter l
  | A1 /\0 A2 => normalize A1 </\0 A2
  end
]]
*)

Print developed.
(** This [development] or factorization lemma necessitate some deep ('well-founded') induction,
using some measure [coherence.length] which shows that this may be related to
arithmetic factorization. *)
Print coherence.length.
(** [[
fix length (A B : objects) (f : arrows A B) {struct f} : nat :=
  match f with
  | unitt _ => 2
  | bracket_left _ _ _ => 4
  | up_1 A0 B0 A1 B1 f1 f2 => length A0 B0 f1 * length A1 B1 f2
  | com A0 B0 C f1 f2 => length A0 B0 f1 + length B0 C f2
  end
]]
*)
Check development: forall (len : nat) (A B : objects) (f : arrows A B),
       length f <= len ->
       {f' : arrows A B &
       (developed f' * ((length f' <= length f) * (f ~~ f')))%type}.

(*
Print developed_normal.
Print developed_normalize.*)

(* begin hide *)
(* begin courtesy cleanup *)
Notation normalize_aux_unitrefl := normalize_aux_arrow.
Notation normalize_unitrefl := normalize_arrow.
(* end courtesy cleanup *)
(* end hide *)

Notation normalize_aux_unitrefl_assoc := normalize_aux_arrow_assoc.
Print normalize_aux_arrow_assoc.
(** [[
fix normalize_aux_arrow_assoc (Y Z : objects) (y : arrows_assoc Y Z)
                              (A : objects) {struct A} :
  arrows_assoc (Y /\0 A) (Z </\0 A) :=
  match A as A0 return (arrows_assoc (Y /\0 A0) (Z </\0 A0)) with
  | letter l => y /\1a unitt_assoc (letter l)
  | A1 /\0 A2 =>
      normalize_aux_arrow_assoc (Y /\0 A1) (Z </\0 A1)
        (normalize_aux_arrow_assoc Y Z y A1) A2 <oa
      bracket_left_assoc Y A1 A2
  end
     : forall Y Z : objects,
       arrows_assoc Y Z ->
       forall A : objects, arrows_assoc (Y /\0 A) (Z </\0 A)
]]
*)

Notation normalize_unitrefl_assoc := normalize_arrow_assoc.
Print normalize_arrow_assoc.
(** [[
fix normalize_arrow_assoc (A : objects) : arrows_assoc A (normalize A) :=
  match A as A0 return (arrows_assoc A0 (normalize A0)) with
  | letter l => unitt_assoc (letter l)
  | A1 /\0 A2 => normalize_aux_unitrefl_assoc (normalize_arrow_assoc A1) A2
  end
     : forall A : objects, arrows_assoc A (normalize A)
]]
*)

Check th151 : forall A : objects, normal A -> normalize A = A.
(** Aborted th270: For local variable [A] with [normal A],
although there is the propositional equality [th151: normalize A = A],
that [normalize A], [A] are not convertible (definitionally/meta equal);
therefore one shall not regard [normalize_unitrefl_assoc], [unitt A] as sharing
the same domain-codomain indices of [arrows_assoc] *)

(* begin hide *)
(* begin explanation *)
Inductive term_unitt_assoc : forall A B : objects, arrows_assoc A B -> Set :=
    term_unitt_assoc_self : forall A : objects,
                             term_unitt_assoc (unitt_assoc A)
  | term_unitt_assoc_at_left : forall (A B : objects) (f : arrows_assoc A B),
                                term_unitt_assoc f ->
                                forall A0 : objects,
                                term_unitt_assoc (f /\1a unitt_assoc A0)
  | term_unitt_assoc_at_right : forall (A A0 B0 : objects)
                                   (f : arrows_assoc A0 B0),
                                 term_unitt_assoc f ->
                                 term_unitt_assoc (unitt_assoc A /\1a f).

Hint Constructors term_unitt_assoc.

Require Import CpdtTactics.

Lemma th270_old_corrected : forall A, normal A -> 
 term_unitt_assoc (normalize_unitrefl_assoc A).

induction 1; crush.
Defined.
(* end explanation *)
(* end hide *)

Check th260 : forall N P : objects, arrows_assoc N P -> normalize N = normalize P.
(** Aborted lemma_coherence_assoc0: For local variables [N], [P] with [arrows_assoc N P],
although there is the propositional equality [th260: normalize N = normalize P],
that [normalize A], [normalize B] are not convertible (definitionally/meta equal);
therefore some transport other than [eq_rect], some coherent transport is lacked. *)

Check normalize_aux_map_assoc
      : forall (X Y : objects) (x : arrows_assoc X Y) (Z : objects)
         (y : arrows_assoc Y Z),
       directed y ->
       forall (A B : objects) (f : arrows_assoc A B),
       {y_map : arrows_assoc (Y </\0 A) (Z </\0 B) &
       ((y_map <oa normalize_aux_unitrefl_assoc x A ~a
         normalize_aux_unitrefl_assoc y B <oa x /\1a f) * directed y_map)%type}.

Check normalize_map_assoc
     : forall (A B : objects) (f : arrows_assoc A B),
       {y_map : arrows_assoc (normalize A) (normalize B) &
       ((y_map <oa normalize_unitrefl_assoc A ~a
         normalize_unitrefl_assoc B <oa f) * directed y_map)%type}.

Print Assumptions normalize_map_assoc.

(** ERRORS OF DOSEN: 1. CONFUSE MIXUP CONVERTIBLE (DEFINITIONALLY/META EQUAL) WITH 
PROPOSITIONAL EQUAL WHEN THE THINGS ARE VARIABLES INSTEAD OF FULLY CONSTRUCTOR-ED
 EXPLICIT TERMS, 2. RELATED TO THIS IS THE COMPUTATIONNALLY WRONG ORDER 
OF HES PRESENTATION *)




(** * Dosen Semiassociative Coherence *)

Print nodes.
(** [[
Inductive nodes : objects -> Set :=
    self : forall A : objects, A
  | at_left : forall A : objects, A -> forall B : objects, A /\0 B
  | at_right : forall A B : objects, B -> A /\0 B.
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
                     x <r y -> at_right C x <r at_right C y.
]]
 *)

Notation comparable A B := {f : arrows_assoc A B | True} (only parsing).

Check bracket_left_on_nodes
     : forall A B C : objects, nodes (A /\0 (B /\0 C)) -> nodes ((A /\0 B) /\0 C).
(** [[

Definition bracket_left_on_nodes (A B C : objects) ( x : nodes (A /\ (B /\ C)) ) : nodes ((A /\ B) /\ C).

dependent destruction x.
exact (at_left (self (A /\ B)) C).
exact (at_left (at_left x B) C).
dependent destruction x.
exact (self ((A /\ B) /\ C)).
exact (at_left (at_right A x) C).
exact (at_right (A /\ B) x).
Defined.
]]
*)

Check arrows_assoc_on_nodes : forall A B : objects, arrows_assoc A B -> nodes A -> nodes B.


(** Soundness. *)

Check lem033 : forall (A B : objects) (f : arrows A B) (x y : A),
       f x <r f y -> x <r y.

(** Completeness. Deep ('well-founded') induction on [lengthn''],
with accumulator/continuation [cumul_letteries]. *)

Check lemma_completeness : forall (B A : objects) (f : arrows_assoc B A)
                                  (H_cumul_lt_right_B : forall x y : nodes B, lt_right x y -> lt_right (f x) (f y))
                           , arrows A B.

Check lem005700: forall (B : objects) (len : nat),
  forall (cumul_letteries : nodes B -> bool)
         (H_cumul_letteries_wellform : cumul_letteries_wellform' B cumul_letteries)
         (H_cumul_letteries_satur : forall y : nodes B, cumul_letteries y = true 
                                                        -> forall z : nodes B, lt_leftorright_eq y z -> cumul_letteries z = true)
         (H_len : lengthn'' cumul_letteries H_cumul_letteries_wellform <= len),
  forall (A : objects) (f : arrows_assoc B A)
         (H_node_is_lettery : forall x : nodes B, cumul_letteries x = true -> node_is_lettery f x)
         (H_object_at_node : forall x : nodes B, cumul_letteries x = true -> object_at_node x = object_at_node (f x))
         (H_cumul_B : forall x y : nodes B, lt_right x y -> lt_right (f x) (f y))
  , arrows A B.

Print Assumptions lem005700.
(** Get two equivalent axioms. *)
(** [[
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type)
                                (x : Q p) (h : p = p), x = eq_rect p Q x p h
]]
*)

Infix "<l" := lt_left (at level 70). 
Print lt_left.

(** Maybe some betterement revision/egition by using [objects_same] is necessary here.
 Contrast this eq with [objects_same] *)
Print lt_leftorright_eq.
(** [[
Notation lt_leftorright_eq x y :=
  (sum (eq x y) (sum (lt_left x y) (lt_right x y))).
]]
*)

(** [nodal_multi_bracket_left_full] below and later really lack this constructive equality [objects_same],
so that we get transport map which are coherent, transport map other than [eq_rect] *)
Print objects_same. 
(** [[
Inductive objects_same : objects -> objects -> Set :=
    objects_same_cons1 : forall l : letters,
                         objects_same (letter l) (letter l)
  | objects_same_cons2 : forall A A' : objects,
                         objects_same A A' ->
                         forall B B' : objects,
                         objects_same B B' ->
                         objects_same (A /\0 B) (A' /\0 B').
]]
*)


(** [nodal_multi_bracket_left_full] is one of the most complicated/multifolded construction
in this coq text. [nodal_multi_bracket_left_full] below and later really lack this constructive equality [objects_same],
so that we get transport map which are coherent, transport map other than [eq_rect] *)

Print "/\\".
(** [[
 fix foldright (A : objects) (Dlist : list objects) {struct Dlist} :
  objects :=
  match Dlist with
  | nil => A
  | (D0 :: Dlist0)%list => foldright A Dlist0 /\0 D0 
]]
*)

Check multi_bracket_left : forall (A B C : objects) (Dlist : list objects),
       arrows (A /\0 (B /\0 C /\\ Dlist)) ((A /\0 B) /\0 C /\\ Dlist).

Check (fun A (x : nodes A) (A2 B2 C2 : objects) (Dlist2 : list objects) =>
    @nodal_multi_bracket_left_full A x A2 B2 C2 Dlist2).


Print object_at_node.
(** [[
object_at_node = 
fix object_at_node (A : objects) (x : A) {struct x} : objects :=
  match x with
  | self A0 => A0
  | at_left A0 x0 _ => object_at_node A0 x0
  | at_right _ B x0 => object_at_node B x0
  end
]]
*)

(** [object_is_letter] is some particularised sigma type so to do 
convertibility (definitinal/meta equality) instantiatiations instead and avoid
propositional equalities. *)
Print object_is_letter.
(** [[
Inductive object_is_letter : objects -> Set :=
    object_is_letter_cons : forall l : letters, object_is_letter (letter l).
]]
*)

Print object_is_tensor.

Print node_is_letter. 
(** [[
Notation node_is_letter x := (object_is_letter (object_at_node x)). 
]]
*)

Print node_is_tensor.
(** [[
Notation node_is_tensor x := (object_is_tensor (object_at_node x)).
]]
*)

Print node_is_lettery. 
(** [[
Notation node_is_lettery f w := 
  (prod
     ( forall (x : nodes _), lt_leftorright_eq w x -> lt_leftorright_eq (f w) (f x) )
     ( forall (x : nodes _), lt_leftorright_eq (f w) (f x) -> lt_leftorright_eq ((rev f) (f w)) ((rev f) (f x)) )).
]]
*)

Print cumul_letteries_wellform'.
(** [[
Notation cumul_letteries_wellform' B cumul_letteries :=
  (forall x : B,
   object_is_letter (object_at_node x) -> eq (cumul_letteries x) true).
]]
*)


Print lengthn'' . 
(** [[
lengthn'' = 
fix lengthn'' (A : objects) (cumul_letteries : A -> bool)
              (H_cumul_letteries_wellform : cumul_letteries_wellform' A
                                              cumul_letteries) {struct A} :
  nat :=
  match
    A as o
    return
      (forall cumul_letteries0 : o -> bool,
       cumul_letteries_wellform' o cumul_letteries0 -> nat)
  with
  | letter l =>
      fun (cumul_letteries0 : letter l -> bool)
        (_ : cumul_letteries_wellform' (letter l) cumul_letteries0) => 1
  | A1 /\0 A2 =>
      fun (cumul_letteries0 : A1 /\0 A2 -> bool)
        (H_cumul_letteries_wellform0 : cumul_letteries_wellform' (A1 /\0 A2)
                                         cumul_letteries0) =>
      let s :=
        Sumbool.sumbool_of_bool (cumul_letteries0 (self (A1 /\0 A2))) in
      if s
      then 1
      else
       let IHA1 :=
         lengthn'' A1 (restr_left cumul_letteries0)
           (restr_left_wellform cumul_letteries0 H_cumul_letteries_wellform0) in
       let IHA2 :=
         lengthn'' A2 (restr_right cumul_letteries0)
           (restr_right_wellform cumul_letteries0 H_cumul_letteries_wellform0) in
       IHA1 + IHA2
  end cumul_letteries H_cumul_letteries_wellform
]]
*)

Check restr_left : forall B1 B2 : objects, (B1 /\0 B2 -> bool) -> B1 -> bool.  
Check restr_left_wellform : forall (B1 B2 : objects) (cumul_letteries : B1 /\0 B2 -> bool),
       cumul_letteries_wellform' (B1 /\0 B2) cumul_letteries ->
       cumul_letteries_wellform' B1 (restr_left cumul_letteries).

(** More at https://github.com/mozert/ . *)
