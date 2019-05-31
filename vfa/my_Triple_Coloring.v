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


Ltac brute_color c H H_good num :=
  try lazymatch goal with
      | [ Hy : ?x = c ?y, Hz : ?x = c ?z |- _] =>
          contradiction (H_good y z); [simpl | rewrite <- Hy ; rewrite <- Hz]; reflexivity
      | [ |- _] => let Cc := fresh "C" in pose proof (H num) as Cc; inversion Cc; brute_color c H H_good (inc num)
      end.

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

Ltac contr h0' h1 h2 h3 h4 h5 h6 c :=
  match goal with
  | [H2 : ?x = c 1, Hn : ?x = c ?n |- type1_triple _ \/ type2_triple _ \/ type3_triple _] =>
      specialize (h0' 1 n);
      rewrite <- h5 in h0'; rewrite <- h2 in h0'; exfalso;
      assert (x <> x -> False);
      [> cbv; try intro; assert (x =x);
      try reflexivity; apply h1; apply h6 |
        apply h1; apply h0'; reflexivity ]
  | [ H3 : ?x = c 2, H4 : ?x = c 3, H5 : ?x = c 4  |- type1_triple _ \/ type2_triple _ \/ type3_triple _] =>
      type1_tac h2 h3 h4 h5
  | [ H3 : ?x = c 2, H5 : ?x = c 4 |- type1_triple _ \/ type2_triple _ \/ type3_triple _] =>
      type2_tac_middle h2 h3 h4 h5
  | [ H4 : ?x = c 3, H5 : ?x = c 4 |- type1_triple _ \/ type2_triple _ \/ type3_triple _] =>
      type2_tac_right h2 h3 h4 h5
  | [ H3 : ?x = c 2, H4 : ?x = c 3 |- type1_triple _ \/ type2_triple _ \/ type3_triple _] =>
      type2_tac_left h2 h3 h4 h5
  | [ H2 : ?x = c 1, H3 : ?y = c 2, H4 : ?z = c 3, H5 : ?w = c 4 |- type1_triple _ \/ type2_triple _ \/ type3_triple _] =>
      type3_tac h2 h3 h4 h5
  end.

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
  remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
    remember H0 as H0'; clear HeqH0';
      contr H0' H1 H2 H3 H4 H5 H6 c.
  - remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
    remember H0 as H0'; clear HeqH0';
      contr H0' H1 H2 H3 H4 H5 H6 c.
  - remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
    remember H0 as H0'; clear HeqH0';
      contr H0' H1 H2 H3 H4 H5 H6 c.
  - remember H as H'''; clear HeqH'''; specialize (H''' 3). inversion H'''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 3).
    rewrite <- H4 in H0'. rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H5.
    apply H1. apply H0'. reflexivity.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
        contr H0' H1 H2 H3 H4 H5 H6 c.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
        contr H0' H1 H2 H3 H4 H5 H6 c.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
        contr H0' H1 H2 H3 H4 H5 H6 c.
  - remember H as H'''; clear HeqH'''; specialize (H''' 3). inversion H'''.
    remember H0 as H0'; clear HeqH0'.
    specialize (H0' 1 3).
    rewrite <- H4 in H0'. rewrite <- H2 in H0'. exfalso.
    assert (1 <> 1 -> False); cbv. try intro. assert (1 =1).
    try reflexivity; apply H1 in H5. apply H1. apply H5.
    apply H1. apply H0'. reflexivity.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
      contr H0' H1 H2 H3 H4 H5 H6 c.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
        contr H0' H1 H2 H3 H4 H5 H6 c.
    + remember H as H''''; clear HeqH''''; specialize (H'''' 4). inversion H'''';
      remember H0 as H0'; clear HeqH0';
        contr H0' H1 H2 H3 H4 H5 H6 c.
  - (* We saw every variant with c 1 = 1, that should be enough *) Admitted.


Close Scope positive.