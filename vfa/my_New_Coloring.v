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
