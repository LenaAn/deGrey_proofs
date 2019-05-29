From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import myGraphs.
From VFA Require Import Graphs_Properties.
From VFA Require Import myColoringSmallGraphs.
From VFA Require Import my_New_Coloring.

Open Scope positive.


(*
Inductive triple (center: node) (border: list node) (g: graph) : Prop :=
  | mk_trip: node -> list node -> graph -> triple center border g.
*)

(* Monochromatic *)
Definition type1_triple (c: Coloring) :=
  let c1 := c 1 in
  let c2 := c 2 in
  ~ (c1 = c2) /\ same_color c 2 3 /\ same_color c 3 4.

(* 2 and 1 *)
Definition type2_triple (c: Coloring) :=
  let c1 := c 1 in
  let c2 := c 2 in
  let c3 := c 3 in 
  let c4 := c 4 in
  ~ (c1 = c2) /\ ~ (c1 = c3) /\ ~ (c1 = c4) /\
    ( (c2 = c3 /\ ~ c2 = c4) \/ (c2 = c4 /\ ~ c2 = c3) \/ (c3 = c4 /\ ~ c3 = c2) ).

Definition type3_triple (c: Coloring) :=
  let c1 := c 1 in
  let c2 := c 2 in
  let c3 := c 3 in 
  let c4 := c 4 in
  ~ (c1 = c2) /\ ~ (c1 = c3) /\ ~ (c1 = c4) /\
    (~ c2 = c3) /\ (~ c2 = c4) /\ (~ c3 = c4).


Definition T := (add_edge 1 2 (add_edge 1 3 (add_edge 1 4 EmptyGraph ) ) ).


Lemma coloring_triple:
  forall c: Coloring, is_good_coloring c T ->
  type1_triple c \/ type2_triple c \/ type3_triple c.
Proof.
  intros. unfold is_good_coloring in H. unfold my_New_Coloring.is_coloring in H. destruct H.
  remember H as H'. clear HeqH'. specialize (H' 1). inversion H';
  remember H as H''; clear HeqH''; specialize (H'' 2); inversion H''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 2);
    rewrite <- H3 in H0'; rewrite <- H2 in H0'; exfalso;
    assert (1 <> 1 -> False); cbv; try intro; assert (1 =1);
    try reflexivity; try apply H1 in H4; try assumption;
    apply H1; apply H0'; reflexivity.
  remember H as H'''; clear HeqH'''. specialize (H''' 3). inversion H'''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 3).
    rewrite <- H4 in H0'. rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H5.
    apply H1. apply H0'. reflexivity.
  remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H''''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 4).
    rewrite <- H5 in H0'. rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H6.
    apply H1. apply H0'. reflexivity.

    Ltac type2_tac_left h2 h3 h4 h5 := right; left; unfold type2_triple;
    rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1;
    left; repeat split; cbv; try intro; try inversion H1.

    Ltac type2_tac_middle h2 h3 h4 h5 := right; left; unfold type2_triple;
    rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1;
    right; left; repeat split; cbv; try intro; try inversion H1.

    Ltac type2_tac_right h2 h3 h4 h5 := right; left; unfold type2_triple;
    rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1;
    right; right; repeat split; cbv; try intro; try inversion H1.

    Ltac type3_tac h2 h3 h4 h5 := right; right; unfold type3_triple;
      rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
      repeat split; cbv; try intro; try inversion H1.

    Ltac type1_tac h2 h3 h4 h5 := left; unfold type1_triple; split;
      try rewrite <- h2; try rewrite <- h3; cbv;
      try intro; try inversion H1;
      unfold same_color; try rewrite <- h3; try rewrite <- h4; try rewrite <- h5;
      split; reflexivity.

  - type1_tac H2 H3 H4 H5.
  - type2_tac_left H2 H3 H4 H5.
  - type2_tac_left H2 H3 H4 H5.
  - remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
    remember H0 as H0'; clear HeqH0';
    specialize (H0' 1 4);
    rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H6.
    apply H1. apply H0'. reflexivity.
    + type2_tac_middle H2 H3 H4 H5.
    + type2_tac_right H2 H3 H4 H5.
    + type3_tac H2 H3 H4 H5.
  - remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
    remember H0 as H0'; clear HeqH0';
    specialize (H0' 1 4);
    rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H6.
    apply H1. apply H0'. reflexivity.
    + type2_tac_middle H2 H3 H4 H5.
    + type3_tac H2 H3 H4 H5.
    + type2_tac_right H2 H3 H4 H5.
  - remember H as H'''; clear HeqH'''; specialize (H''' 3). inversion H'''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 3).
    rewrite <- H4 in H0'. rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H5.
    apply H1. apply H0'. reflexivity.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      specialize (H0' 1 4);
      rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
      assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
      try reflexivity; apply H1 in H5. apply H1. apply H6.
      apply H1. apply H0'. reflexivity.
      * type2_tac_right H2 H3 H4 H5.
      * type2_tac_middle H2 H3 H4 H5.
      * type3_tac H2 H3 H4 H5.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      specialize (H0' 1 4);
      rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
      assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
      try reflexivity; apply H1 in H5. apply H1. apply H6.
      apply H1. apply H0'. reflexivity.
      * type2_tac_left H2 H3 H4 H5.
      * type1_tac H2 H3 H4 H5.
      * type2_tac_left H2 H3 H4 H5.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      specialize (H0' 1 4);
      rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
      assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
      try reflexivity; apply H1 in H5. apply H1. apply H6.
      apply H1. apply H0'. reflexivity.
        * type3_tac H2 H3 H4 H5.
        * type2_tac_middle H2 H3 H4 H5.
        * type2_tac_right H2 H3 H4 H5.
  - remember H as H'''; clear HeqH'''; specialize (H''' 3). inversion H'''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 3).
    rewrite <- H4 in H0'. rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H5.
    apply H1. apply H0'. reflexivity.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      specialize (H0' 1 4);
      rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
      assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
      try reflexivity; apply H1 in H5. apply H1. apply H6.
      apply H1. apply H0'. reflexivity.
      * type2_tac_right H2 H3 H4 H5.
      * type3_tac H2 H3 H4 H5.
      * type2_tac_middle H2 H3 H4 H5.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      specialize (H0' 1 4);
      rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
      assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
      try reflexivity; apply H1 in H5. apply H1. apply H6.
      apply H1. apply H0'. reflexivity.
      * type3_tac H2 H3 H4 H5.
      * type2_tac_right H2 H3 H4 H5.
      * type2_tac_middle H2 H3 H4 H5.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      specialize (H0' 1 4);
      rewrite <- H5 in H0'; rewrite <- H2 in H0'. exfalso.
      assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
      try reflexivity; apply H1 in H5. apply H1. apply H6.
      apply H1. apply H0'. reflexivity.
      * type2_tac_left H2 H3 H4 H5.
      * type2_tac_left H2 H3 H4 H5.
      * type1_tac H2 H3 H4 H5.
  - (* We saw every variant with c 1 = 1, that should be enough *) Admitted.


Close Scope positive.