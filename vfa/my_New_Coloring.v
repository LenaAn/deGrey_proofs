Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.Lists.ListSet.
Require Export Coq.Numbers.BinNums.
Export ListNotations.
From VFA Require Import Color.
From VFA Require Import myGraphs.

Open Scope positive.
Definition Coloring := positive -> positive.

Definition col1 : Coloring :=
  fun x => match x with 
            | 1 => 2
            | _ => 1
          end.

Compute col1 2.
Compute col1 1.

Definition same_color_b (c : Coloring) (u v : positive) : bool := c u =? c v.
Definition same_color (c : Coloring) (u v : positive) : Prop := c u = c v.

Inductive is_color : positive -> Prop :=
| c1: is_color 1%positive
| c2: is_color 2%positive
| c3: is_color 3%positive
| c4: is_color 4%positive
.

Definition EmptyColoring (default: positive): Coloring :=
  fun _ => default.

Compute is_color ((EmptyColoring 5) 1).

Definition is_coloring (c : Coloring) (g: graph) := 
  forall x : positive, S.In x (nodes g) -> is_color (c x).

Compute is_coloring (EmptyColoring 5) H.

Definition is_good_coloring (c : Coloring) (g : graph) :=
  is_coloring c g /\ forall x y : positive, S.In y (adj g x) -> c x <> c y.

Definition is_colorable (g : graph) :=
  exists c : Coloring, is_good_coloring c g.

Definition t_update (c : Coloring) (n : node) (clr : positive) :=
  fun x' => if n =? x' then clr else c x'.

Close Scope positive.