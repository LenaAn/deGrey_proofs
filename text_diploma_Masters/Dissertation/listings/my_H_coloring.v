From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import myGraphs.
From VFA Require Import Graphs_Properties.
From VFA Require Import myColoringSmallGraphs.
From VFA Require Import my_New_Coloring.
From VFA Require Import my_Triple_Coloring.

Open Scope positive.


(* Type1 - Type1 *)
Definition type1_H (c: Coloring) : Prop :=
  type1_triple [1; 2; 4; 6] c /\ type1_triple [1; 3; 5; 7] c /\
    ~ same_color c 2 3.

(* Type1 - Type2 *)
Definition type2_H (c: Coloring) : Prop :=
  (type1_triple [1; 2; 4; 6] c /\ type2_triple [1; 3; 5; 7] c /\
    ~ same_color c 2 3 /\ ~ same_color c 2 5 /\ ~ same_color c 2 7) \/
  (type2_triple [1; 2; 4; 6] c /\ type1_triple [1; 3; 5; 7] c /\
    ~ same_color c 2 3 /\ ~ same_color c 4 3 /\ ~ same_color c 6 3).

(* Diagonals are monochromatic *)
Definition type3_H (c: Coloring) : Prop :=
  type3_triple [1; 2; 4; 6] c /\ type3_triple [1; 3; 5; 7] c /\
    same_color c 2 5 /\ same_color c 3 6 /\ same_color c 4 7.


(* One diagonal and same colors close to the vert in diagonal *)
Definition type4_H (c: Coloring) : Prop :=
  type2_triple [1; 2; 4; 6] c /\ type2_triple [1; 3; 5; 7] c /\
  (
    (* Diagonal is 2 5 *) 
    (same_color c 2 5 /\ same_color c 3 7 /\ same_color c 4 6 ) \/

    (* Diagonal is 3 6 *) 
    (same_color c 3 6 /\ same_color c 2 4 /\ same_color c 5 7 ) \/

    (* Diagonal is 4 7 *) 
    (same_color c 4 7 /\ same_color c 3 5 /\ same_color c 2 6 )
  ).

Ltac contr H0 Hn Hm n m x :=
  let H1 := fresh in
  let H6 := fresh in
  remember H0 as H0' eqn:HeqH0'; clear HeqH0';
  specialize (H0' n m);
  rewrite <- Hn in H0'; rewrite <- Hm in H0'; exfalso;
  assert (x <> x -> False);
  [> cbv; try intro; assert (x =x);
  try reflexivity; apply H1; apply H6 |
    apply H1; apply H0'; reflexivity ].


Ltac find_contr H0 c :=
  lazymatch goal with
  | [H2 : ?x = c 1, Hn : ?x = c ?n |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _] =>
      contr H0 H2 Hn 1 n x
  | [Hn : ?x = c ?n, Hm : ?x = c ?m, Hk : ?x = c ?k |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _] =>
      try contr H0 Hn Hm n m x; try contr H0 Hn Hk n k x;
      try contr H0 Hm Hk m k x
  | [Hn : ?x = c ?n, Hm : ?x = c ?m |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _] =>
      contr H0 Hn Hm n m x
  end.

Ltac color_next H n :=
  let H' := fresh in
  let HeqH' := fresh in
  remember H as H' eqn: HeqH'; clear HeqH';  specialize (H' n); inversion H'.

Ltac use_color H3 H5 H7 H9 H11 H13 H15 :=
  try rewrite <- H3;
  try rewrite <- H5;
  try rewrite <- H7;
  try rewrite <- H9;
  try rewrite <- H11;
  try rewrite <- H13;
  try rewrite <- H15.

Ltac trivia_cases H3 H5 H7 H9 H11 H13 H15 :=
  repeat split; simpl; unfold same_color;
  use_color H3 H5 H7 H9 H11 H13 H15;
  try discriminate; try reflexivity.

Ltac type1_H_tac H3 H5 H7 H9 H11 H13 H15 :=
  left; unfold type1_H;
  trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type2_H_tac_left_left H3 H5 H7 H9 H11 H13 H15 :=
  right; left; unfold type2_H;
  (* Choose types of triples *)
    left; trivia_cases H3 H5 H7 H9 H11 H13 H15;
  (* Chose the different color in Type2 *)
    left; split; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type2_H_tac_left_right H3 H5 H7 H9 H11 H13 H15 :=
  right; left; unfold type2_H;
  (* Choose types of triples *)
    left; trivia_cases H3 H5 H7 H9 H11 H13 H15;
  (* Chose the different color in Type2 *)
    right; right; split; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type2_H_tac_left_middle H3 H5 H7 H9 H11 H13 H15 :=
  right; left; unfold type2_H;
  (* Choose types of triples *)
    left; trivia_cases H3 H5 H7 H9 H11 H13 H15;
  (* Chose the different color in Type2 *)
    right; left; split; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type2_H_tac_right_left H3 H5 H7 H9 H11 H13 H15 :=
  right; left; unfold type2_H;
    right; trivia_cases H3 H5 H7 H9 H11 H13 H15;
    left; split; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type2_H_tac_right_middle H3 H5 H7 H9 H11 H13 H15 :=
  right; left; unfold type2_H;
    right; trivia_cases H3 H5 H7 H9 H11 H13 H15;
    right; left; split; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type2_H_tac_right_right H3 H5 H7 H9 H11 H13 H15 :=
  right; left; unfold type2_H;
    right; trivia_cases H3 H5 H7 H9 H11 H13 H15;
    repeat right; split; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type3_H_tac H3 H5 H7 H9 H11 H13 H15 :=
  right; right; left; trivia_cases H3 H5 H7 H9 H11 H13 H15.

Ltac type4_H_tac_1 H3 H5 H7 H9 H11 H13 H15 :=
  repeat right; unfold type4_H;
  trivia_cases H3 H5 H7 H9 H11 H13 H15;
  [> repeat right; trivia_cases H3 H5 H7 H9 H11 H13 H15 |
     right; left; trivia_cases H3 H5 H7 H9 H11 H13 H15 |
     left; trivia_cases H3 H5 H7 H9 H11 H13 H15
  ].

Ltac type4_H_tac_2 H3 H5 H7 H9 H11 H13 H15 :=
  repeat right; unfold type4_H;
  trivia_cases H3 H5 H7 H9 H11 H13 H15;
  [> left; trivia_cases H3 H5 H7 H9 H11 H13 H15 |
     repeat right; trivia_cases H3 H5 H7 H9 H11 H13 H15 |
     right; left; trivia_cases H3 H5 H7 H9 H11 H13 H15
  ].

Ltac type4_H_tac_3 H3 H5 H7 H9 H11 H13 H15 :=
  repeat right; unfold type4_H;
  trivia_cases H3 H5 H7 H9 H11 H13 H15;
  [> right; left; trivia_cases H3 H5 H7 H9 H11 H13 H15 |
     left; trivia_cases H3 H5 H7 H9 H11 H13 H15 |
     repeat right; trivia_cases H3 H5 H7 H9 H11 H13 H15
  ].

Ltac find_type H3 H5 H7 H9 H11 H13 H15 c :=
  match goal with
    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x2 = c 4, H11 : ?x3 = c 5, H13 : ?x2 = c 6,
        H15 : ?x3 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type1_H_tac H3 H5 H7 H9 H11 H13 H15

    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x2 = c 4, H11 : ?x3 = c 5, H13 : ?x2 = c 6,
        H15 : ?x4 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type2_H_tac_left_left H3 H5 H7 H9 H11 H13 H15
    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x2 = c 4, H11 : ?x4 = c 5, H13 : ?x2 = c 6,
        H15 : ?x3 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type2_H_tac_left_middle H3 H5 H7 H9 H11 H13 H15
    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x2 = c 4, H11 : ?x4 = c 5, H13 : ?x2 = c 6,
        H15 : ?x4 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type2_H_tac_left_right H3 H5 H7 H9 H11 H13 H15

    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x2 = c 4, H11 : ?x3 = c 5, H13 : ?x4 = c 6,
        H15 : ?x3 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type2_H_tac_right_left H3 H5 H7 H9 H11 H13 H15
    | [ H3: ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x4 = c 4, H11 : ?x3 = c 5, H13 : ?x2 = c 6,
        H15 : ?x3 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type2_H_tac_right_middle H3 H5 H7 H9 H11 H13 H15
    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x4 = c 4, H11 : ?x3 = c 5, H13 : ?x4 = c 6,
        H15 : ?x3 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type2_H_tac_right_right H3 H5 H7 H9 H11 H13 H15

    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x4 = c 4, H11 : ?x2 = c 5, H13 : ?x3 = c 6,
        H15 : ?x4 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type3_H_tac H3 H5 H7 H9 H11 H13 H15

    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x4 = c 4, H11 : ?x2 = c 5, H13 : ?x4 = c 6,
        H15 : ?x3 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type4_H_tac_1 H3 H5 H7 H9 H11 H13 H15
    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x2 = c 4, H11 : ?x4 = c 5, H13 : ?x3 = c 6,
        H15 : ?x4 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type4_H_tac_2 H3 H5 H7 H9 H11 H13 H15
    | [ H3 : ?x1 = c 1, H5 : ?x2 = c 2, H7 : ?x3 = c 3,
        H9 : ?x4 = c 4, H11 : ?x3 = c 5, H13 : ?x2 = c 6,
        H15 : ?x4 = c 7 |- type1_H _ \/ type2_H _ \/ type3_H _ \/ type4_H _ ] =>
          type4_H_tac_3 H3 H5 H7 H9 H11 H13 H15
  end.

Lemma coloring_H:
  forall c: Coloring, is_good_coloring c H ->
  type1_H c \/ type2_H c \/ type3_H c \/ type4_H c.
Proof.
  intros. unfold is_good_coloring in H. unfold is_coloring in H. destruct H.
  color_next H 1;
    color_next H 2; try find_contr H0 c;
      color_next H 3; try find_contr H0 c;
        color_next H 4; try find_contr H0 c;
          color_next H 5; try find_contr H0 c;
            color_next H 6; try find_contr H0 c;
              color_next H 7; try find_contr H0 c;
                find_type H3 H5 H7 H9 H11 H13 H15 c.
Qed.

Close Scope positive.
