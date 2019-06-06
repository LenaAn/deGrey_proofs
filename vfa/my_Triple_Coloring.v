From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import myGraphs.
From VFA Require Import Graphs_Properties.
From VFA Require Import myColoringSmallGraphs.
From VFA Require Import my_New_Coloring.

Open Scope positive.


Compute nth 0 [1;2;3] 1.

(* Monochromatic *)
Definition type1_triple (el: list node) (c: Coloring) :=
  let center := nth 0 el 1 in
  let v1 := nth 1 el 1 in
  let v2 := nth 2 el 1 in
  let v3 := nth 3 el 1 in
  let c1 := c center in
  let c2 := c v1 in
  ~ (c1 = c2) /\ same_color c v1 v2 /\ same_color c v2 v3.

(* 2 and 1 *)
Definition type2_triple (el: list node) (c: Coloring) :=
  let center := nth 0 el 1 in
  let v1 := nth 1 el 1 in
  let v2 := nth 2 el 1 in
  let v3 := nth 3 el 1 in

  let c1 := c center in
  let c2 := c v1 in
  let c3 := c v2 in 
  let c4 := c v3 in
  ~ (c1 = c2) /\ ~ (c1 = c3) /\ ~ (c1 = c4) /\
    ( (c2 = c3 /\ ~ c2 = c4) \/ (c2 = c4 /\ ~ c2 = c3) \/ (c3 = c4 /\ ~ c3 = c2) ).

Definition type3_triple (el: list node) (c: Coloring) :=
  let center := nth 0 el 1 in
  let v1 := nth 1 el 1 in
  let v2 := nth 2 el 1 in
  let v3 := nth 3 el 1 in

  let c1 := c center in
  let c2 := c v1 in
  let c3 := c v2 in 
  let c4 := c v3 in
  ~ (c1 = c2) /\ ~ (c1 = c3) /\ ~ (c1 = c4) /\
    (~ c2 = c3) /\ (~ c2 = c4) /\ (~ c3 = c4).


Ltac type2_tac_left h2 h3 h4 h5 := right; left; unfold type2_triple;
    simpl; rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1;
    left; repeat split; cbv; try intro; simpl; try inversion H1.

Ltac type2_tac_middle h2 h3 h4 h5 := right; left; unfold type2_triple;
    simpl; rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1;
    right; left; repeat split; cbv; try intro; simpl; try inversion H1.

Ltac type2_tac_right h2 h3 h4 h5 := right; left; unfold type2_triple;
    simpl; rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1;
    right; right; repeat split; cbv; try intro; simpl; try inversion H1.

Ltac type3_tac h2 h3 h4 h5 := right; right; unfold type3_triple;
    simpl; rewrite <- h2; rewrite <- h3; rewrite <- h4; rewrite <- h5;
    repeat split; cbv; try intro; try inversion H1.

Ltac type1_tac h2 h3 h4 h5 := left; unfold type1_triple; split;
    simpl; try rewrite <- h2; try rewrite <- h3; cbv;
    try intro; try inversion H1;
    unfold same_color; try rewrite <- h3; try rewrite <- h4; try rewrite <- h5;
    split; reflexivity.

Ltac contr h0' h2 h3 h4 h5 c :=
  match goal with
  | [H2 : ?x = c 1, Hn : ?x = c ?n |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
      let H1 := fresh in
      let H6 := fresh in
      specialize (h0' 1 n);
      rewrite <- h5 in h0'; rewrite <- h2 in h0'; exfalso;
      assert (x <> x -> False);
      [> cbv; try intro; assert (x =x);
      try reflexivity; apply H1; apply H6 |
        apply H1; apply h0'; reflexivity ]
  | [ H3 : ?x = c 2, H4 : ?x = c 3, H5 : ?x = c 4  |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
      type1_tac h2 h3 h4 h5
  | [ H3 : ?x = c 2, H5 : ?x = c 4 |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
      type2_tac_middle h2 h3 h4 h5
  | [ H4 : ?x = c 3, H5 : ?x = c 4 |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
      type2_tac_right h2 h3 h4 h5
  | [ H3 : ?x = c 2, H4 : ?x = c 3 |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
      type2_tac_left h2 h3 h4 h5
  | [ H2 : ?x = c 1, H3 : ?y = c 2, H4 : ?z = c 3, H5 : ?w = c 4 |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
      type3_tac h2 h3 h4 h5
  end.


Ltac level3 h h0' h0 h2 h3 h4 c :=
  match goal with
  | [ H2 : ?x = c 1, H4 : ?x = c 3 |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
    let Ha := fresh in
      specialize (h0' 1 3);
        rewrite <- h4 in h0'; rewrite <- h2 in h0'; exfalso;
        assert (x <> x -> False);
          [> cbv; intro Ha; assert (x = x) as H5 ;
            [> try reflexivity |
               apply Ha in H5; apply H5 ]
            | apply Ha; apply h0'; reflexivity ]
  | [ |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
    remember h as H'''' eqn:HeqH'''' ; clear HeqH''''; specialize (H'''' (3+1)); inversion H'''' as [H5|H5|H5|H5];
        remember h0 as h0'' eqn:HeqH0' ; clear HeqH0';
           contr  h0'' h2 h3 h4 H5 c
  end.

Ltac level2 h h0' h0 h2 h3 c :=
  match goal with
  | [ H2 : ?x = c 1, H4 : ?x = c 2 |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
    let Ha := fresh in
      specialize (h0' 1 2);
        rewrite <- h3 in h0'; rewrite <- h2 in h0'; exfalso;
        assert (x <> x -> False);
          [> cbv; intro Ha; assert (x = x) as H5 ;
            [> try reflexivity |
               apply Ha in H5; apply H5 ]
            | apply Ha; apply h0'; reflexivity ]
  | [ |- type1_triple _ _ \/ type2_triple _ _ \/ type3_triple _ _] =>
    remember h as H''' eqn:HeqH''' ; clear HeqH'''; specialize (H''' (2+1)); inversion H''' as [H4|H4|H4|H4];
        remember h0 as Ha eqn:HeqH0 ; clear HeqH0;
           level3 h Ha h0 h2 h3 H4 c
  end.


Definition T := mk_graph [ (1, 2); (1, 3); (1, 4) ].

Lemma coloring_triple_T:
  forall c: Coloring, is_good_coloring c T ->
  type1_triple [1; 2; 3; 4] c \/ type2_triple [1; 2; 3; 4] c \/ type3_triple [1; 2; 3; 4] c.
Proof.
  intros. unfold is_good_coloring in H. unfold my_New_Coloring.is_coloring in H. destruct H.
  remember H as H'. clear HeqH'. specialize (H' 1). inversion H';
    remember H as H''; clear HeqH''; specialize (H'' 2); inversion H''; remember H0 as H0'; clear HeqH0';
      level2 H H0' H0 H2 H3 c.
Qed.

Close Scope positive.