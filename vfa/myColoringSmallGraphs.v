From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import myGraphs.


Open Scope positive.


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

Definition is_type1 (palette: S.t) (g: graph) (f: coloring) : Prop :=
  exists a b, is_the_triple a /\ is_the_triple b /\ not_equal_triple a b /\
      is_monocromathic_triple a /\ is_monocromathic_triple b.

Theorem H_in_4_colors:
  forall f: coloring,
  coloring_ok palette4 H f -> 
    xorb is_type1 palette4 H f
      (xorb is_type2
        (xorb is_type3 is_type4)
      )
    .


Close Scope positive.