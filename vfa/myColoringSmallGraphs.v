From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import myGraphs.
From VFA Require Import Graphs_Properties.


Open Scope positive.

(* Monochromatic triplet in H with center. *)

Definition center (g : graph) (o : node) : Prop :=
  forall i, S.In i (nodes g) -> (i <> o) -> edge g i o.

Lemma node1_is_center_H:
   center H 1%positive.
Proof.
  unfold center. intros. unfold edge. gr_destr H; try reflexivity.
  - destruct H0.  reflexivity.
Qed.

Lemma center_H_is_1:
   forall n, S.In n (nodes H) -> (n <> 1) ->  ~ (center H n).
Proof.
  intros. gr_destr H.
  - unfold center; unfold not; intros; specialize (H 2); compute in H;
    try discriminate H; try reflexivity; intros; try discriminate H2.
  - unfold center; unfold not; intros; specialize (H 5); compute in H;
    try discriminate H; try reflexivity; intros; try discriminate H2.
  - unfold center; unfold not; intros; specialize (H 2); compute in H;
    try discriminate H; try reflexivity; intros; try discriminate H2.
  - destruct H0. reflexivity.
  - unfold center; unfold not; intros; specialize (H 2); compute in H;
    try discriminate H; try reflexivity; intros; try discriminate H2.
  - unfold center; unfold not; intros; specialize (H 5); compute in H;
    try discriminate H; try reflexivity; intros; try discriminate H2.
  - unfold center; unfold not; intros; specialize (H 5); compute in H;
    try discriminate H; try reflexivity; intros; try discriminate H2.
Qed.

Definition H_center (o : node) : Prop :=
  (gr_deg H o) = 6%nat.

Compute (gr_deg H 1).

Compute gr_show H.

(*
Lemma H_center_iff : forall o, center H o <-> o = 1.
Proof.
split; intro.
- apply center_H_is_1. unfold center in H. Print H. Admitted.
(*-  rewrite H. reflexivity.
Qed. *)
*)

Check subset_nodes.

Definition gr_deg_search (g : graph) (d : nat) : nodeset :=
  subset_nodes (fun _ a => Nat.eqb (S.cardinal a) d) g.

Compute S.elements (gr_deg_search H 0).
Compute S.elements (gr_deg_search H 3).


Fixpoint gr_deg_sort (g : graph) (maxd : nat) : list (list node) :=
  match maxd with
  | 0%nat => [S.elements (gr_deg_search g 0)]
  | S n => S.elements (gr_deg_search g maxd) :: gr_deg_sort g n
  end.

Compute gr_deg_sort H 6.


Definition node_color (clr : coloring) (n : node) (c : S.elt) :=
  M.find n clr = Some c.


Definition monochrom (g : graph) (clr : coloring) (o l m n : node) :=
  edge g o l /\ edge g o m /\ edge g o n /\ 
   exists c, (node_color clr l c /\ node_color clr m c /\ node_color clr n c).

(* To prove the next lemma I need smth like this *)
Lemma adj_not_same_color : 
  forall (a b : node) (clr: coloring) (plt : S.t) (g: graph),
    coloring_ok plt g clr ->
    (exists c, (node_color clr a c /\ node_color clr a c) ) -> ~ edge g a b.
Proof.
  Admitted.


(* Why I need this?  *)
(* Can't do this now *)
Lemma H_monochrom_center : forall (plt : S.t) (clr : coloring) (o l m n : node),
  coloring_ok plt H clr -> monochrom H clr o l m n -> H_center o.
Proof.
  Admitted.


Search ( _  In  ).

Print last.

Definition is_cycle (el : list node) (g: graph) : Prop :=
  let prev := last el 1 in
  fst (fold_left (fun flag_prev x =>
                  let flag := fst flag_prev in
                  let prev := snd flag_prev in
                  (flag /\ (S.In x (adj g prev)),
                    x)
            )
            el
            (True, prev)
      ).

(*
Definition b_is_cycle (el : list node) (g: graph) : bool :=
  let prev := last el 1 in
  fst (fold_left (fun flag_prev x =>
                  let flag := fst flag_prev in
                  let prev := snd flag_prev in
                  ( andb flag (existsb x (S.elements (adj g prev))) ,
                    x)
            )
            el
            (true, prev)
      ).
*)

Compute gr_show H.

Compute is_cycle [2;3;4;5;6;7] H.
Compute is_cycle [2;3;5;6;7] H.

Definition center_to_all (center: node) (el : list node) (g: graph) : Prop :=
  fold_left (fun flag x => flag /\ S.In x (adj g center)) el True.

Compute center_to_all 1 [2;3;4;5] H.
Compute center_to_all 2 [2;3;4;5] H.

Search ( _ positive _ nat).


Definition not_adjacent (a b: node) (g: graph) : Prop :=
  ~ (S.In b (adj g a) /\ S.In a (adj g b)).

Check nth. 

Compute nth 2 [1; 2; 3].

Close Scope positive.

Definition all_3_not_adjacent (el: list node) (g: graph) : Prop :=
  (length el =? 3) = true /\
  let a := nth 0 el 1%positive in
  let b := nth 1 el 1%positive in
  let c := nth 2 el 1%positive in
  not_adjacent a b g /\
  not_adjacent b c g /\
  not_adjacent a c g.

Definition is_the_triple (border: list node) (center: node) (g: graph) : Prop :=
  length border =? 3 = true /\
  center_to_all center border g /\
  all_3_not_adjacent border g.


Open Scope positive.

(* Compute center_to_all 1%positive [2;3;4;5] H.
Compute center_to_all 2 [2;3;4;5] H.
*)

Definition palette4: S.t := 
  fold_right S.add S.empty [1; 2; 3; 4].

Print In.

Definition not_equal_triple(border1: list node)
    (border2: list node) : Prop :=
  (exists a, In a border1 /\  ~ In a border2) \/ 
    (exists a, In a border2 /\  ~ In a border1).


Close Scope positive.


Definition is_monocromathic_triple (el: list node) (f: coloring) : Prop :=
  is_the_triple el 1%positive H /\
  (let a := nth 0 el 1%positive in
   let b := nth 1 el 1%positive in
   let c := nth 2 el 1%positive in
    exists cl, (node_color f a cl /\ node_color f b cl /\ node_color f c cl)).


Definition is_type1 (palette: S.t) (g: graph) (f: coloring) : Prop :=
  exists a b, 
    is_the_triple a 1%positive H /\ is_the_triple b 1%positive H /\ 
      not_equal_triple a b /\
        is_monocromathic_triple a f /\ is_monocromathic_triple b f.

Definition is_type2 (palette: S.t) (g: graph) (f: coloring) : Prop :=
  exists a b, 
    is_the_triple a 1%positive H /\ is_the_triple b 1%positive H /\ 
      not_equal_triple a b /\
        is_monocromathic_triple a f /\ ~is_monocromathic_triple b f.

Definition is_type_3_4 (palette: S.t) (g: graph) (f: coloring) : Prop :=
  forall a,
    is_the_triple a 1%positive H -> ~is_monocromathic_triple a f.

Definition xor (A: Prop) (B: Prop) : Prop :=
  (A \/ B) /\ (~A \/ ~B).

Definition coloring_total_ok (palette: S.t) (g: graph) (f: coloring) :=
  coloring_ok (palette: S.t) (g: graph) (f: coloring) /\ 
    forall i, S.In i (nodes g) -> exists c, node_color f i c.


Theorem tr :
  (True -> False) -> False.
Proof.
  intros. apply H. reflexivity.
Qed.


Print S.In.
Theorem H_in_4_colors:
  forall f: coloring,
  coloring_total_ok palette4 H f -> 
    or (is_type1 palette4 H f)
        (or (is_type2 palette4 H f) (is_type_3_4 palette4 H f)).
Proof.
  intros [|H].
  - intros. unfold coloring_total_ok in H. destruct H.
    remember H0 as H0'. clear HeqH0'.
    specialize (H0 2%positive). compute in H0. exfalso. generalize dependent H0.
    intro. assert (true = true).
    + reflexivity.
    + apply H0 in H1. inversion H1. inversion H2.
  - (* This way is not getting us any further*) Admitted.


Close Scope positive.