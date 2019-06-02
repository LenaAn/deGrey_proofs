Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Lists.ListSet.
Require Export Coq.Numbers.BinNums.
Export ListNotations.
From VFA Require Import Color.

Definition Coloring := positive -> positive.
Definition same_color (c : Coloring) (u v : positive) : Prop := c u = c v.

Inductive is_color : positive -> Prop :=
| c1: is_color 1%positive
| c2: is_color 2%positive
| c3: is_color 3%positive
| c4: is_color 4%positive
.

Definition is_coloring (c : Coloring) := forall x : positive, is_color (c x).

Definition is_good_coloring (c : Coloring) (g : graph) :=
  is_coloring c /\ forall x y : positive, S.In y (adj g x) -> c x <> c y.

Definition is_colorable (g : graph) :=
  exists c : Coloring, is_good_coloring c g.
