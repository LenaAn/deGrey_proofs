Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Lists.ListSet.
Require Export Coq.Numbers.BinNums.
Export ListNotations.

Definition eq_dec : forall x y : positive, {x = y} + {x <> y}.
  decide equality.
Defined.

Print eq_dec.

Definition Coloring := positive -> positive.
Definition same_color (c : Coloring) (u v : positive) : Prop := c u = c v.

Inductive is_color : positive -> Prop :=
| c1: is_color 1%positive
| c2: is_color 2%positive
| c3: is_color 3%positive
| c4: is_color 4%positive
.

Definition is_coloring (c : Coloring) := forall x : positive, is_color (c x).

Fixpoint beq_pos (u v : positive) :=
  match u, v with
  | xH, xH => true
  | xO x, xO y => beq_pos x y
  | xI x, xI y => beq_pos x y
  | _, _ => false
  end.

Definition Graph := positive -> set positive.
Definition EmptyGraph : Graph := fun (x : positive) => (empty_set positive).
Definition add_edge (u v : positive) (g : Graph) : Graph := fun (x : positive) =>
  if beq_pos x u then set_add eq_dec v (g u) else
    if beq_pos x v then set_add eq_dec u (g v) else
      g x.

Definition is_good_coloring (c : Coloring) (g : Graph) :=
  is_coloring c /\ forall x y : positive, set_mem eq_dec y (g x) = true -> c x <> c y.

Definition is_colorable (g : Graph) :=
  exists c : Coloring, is_good_coloring c g.

Fixpoint inc (x : positive) : positive :=
  match x with
  | xH => 2%positive
  | xO x => xI x
  | xI x => xO (inc x)
  end.

Ltac brute_color c H H_good num :=
  try lazymatch goal with
      | [ Hy : ?x = c ?y, Hz : ?x = c ?z |- _] =>
          contradiction (H_good y z); [simpl | rewrite <- Hy ; rewrite <- Hz]; reflexivity
      | [ |- _] => let Cc := fresh "C" in pose proof (H num) as Cc; inversion Cc; brute_color c H H_good (inc num)
      end.

Example test01: let G := (add_edge 1 2 (add_edge 1 3 (add_edge 1 4 (add_edge 1 5
                                       (add_edge 2 3 (add_edge 2 4 (add_edge 2 5
                                                     (add_edge 3 4 (add_edge 3 5
                                                                   (add_edge 4 5 EmptyGraph))))))))))
  in ~ is_colorable G.
Proof.
  intro G.
  unfold is_colorable.
  intro.
  inversion_clear H.
  rename x into c.
  inversion_clear H0.
  rename H1 into H_good.
  brute_color c H H_good 1%positive.
Qed.

(*
  inversion C1.
  {
    inversion C2.
    {
      contradiction (H_good 1%positive 2%positive); [simpl | rewrite <- H1 ; rewrite <- H2]; reflexivity.
    }
    {
      inversion C3.
      {
        contradiction (H_good 1%positive 3%positive); [simpl | rewrite <- H1 ; rewrite <- H3]; reflexivity.
      }
      {
        contradiction (H_good 2%positive 3%positive); [simpl | rewrite <- H2 ; rewrite <- H3]; reflexivity.
      }
      {
        inversion C4.
        {
          contradiction (H_good 1%positive 4%positive); [simpl | rewrite <- H1 ; rewrite <- H4]; reflexivity.
        }
        {
          contradiction (H_good 2%positive 4%positive); [simpl | rewrite <- H2 ; rewrite <- H4]; reflexivity.
        }
        {
          contradiction (H_good 3%positive 4%positive); [simpl | rewrite <- H3 ; rewrite <- H4]; reflexivity.
        }
        {
          inversion C5.
          {
            contradiction (H_good 1%positive 5%positive); [simpl | rewrite <- H1 ; rewrite <- H5]; reflexivity.
          }
          {
            contradiction (H_good 2%positive 5%positive); [simpl | rewrite <- H2 ; rewrite <- H5]; reflexivity.
          }
          {
            contradiction (H_good 3%positive 5%positive); [simpl | rewrite <- H3 ; rewrite <- H5]; reflexivity.
          }
          {
            contradiction (H_good 4%positive 5%positive); [simpl | rewrite <- H4 ; rewrite <- H5]; reflexivity.
          }
        }
      }
      {
        inversion C4.
        {
          contradiction (H_good 1%positive 4%positive); [simpl | rewrite <- H1 ; rewrite <- H4]; reflexivity.
        }
        {
          contradiction (H_good 2%positive 4%positive); [simpl | rewrite <- H2 ; rewrite <- H4]; reflexivity.
        }
        {
          inversion C5.
          {
            contradiction (H_good 1%positive 5%positive); [simpl | rewrite <- H1 ; rewrite <- H5]; reflexivity.
          }
          {
            contradiction (H_good 2%positive 5%positive); [simpl | rewrite <- H2 ; rewrite <- H5]; reflexivity.
          }
          {
            contradiction (H_good 4%positive 5%positive); [simpl | rewrite <- H4 ; rewrite <- H5]; reflexivity.
          }
          {
            contradiction (H_good 3%positive 5%positive); [simpl | rewrite <- H3 ; rewrite <- H5]; reflexivity.
          }
        }
        {
          contradiction (H_good 3%positive 4%positive); [simpl | rewrite <- H3 ; rewrite <- H4]; reflexivity.
        }
      }
*)