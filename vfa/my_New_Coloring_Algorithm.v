From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import myGraphs.
From VFA Require Import my_New_Coloring.


Open Scope positive.

Print H.
Compute gr_show H.

Definition color_next(g: graph) (c: Coloring) (next: node) 
  (default: positive) (default_overflow: positive) :=
  let cur_color := c next in
  if (cur_color =? default)
    then t_update c next 1
    else if cur_color =? 4
      then t_update c next default_overflow
      else t_update c next (cur_color+1).

Definition is_contr (g: graph) (c: Coloring) (last: node)
  (default: positive) (default_overflow: positive) : bool :=
    let last_color := c last in
    let last_neigh := adj g last in
    if last_color =? default_overflow
      then false
      else S.fold
            (fun x flag => orb flag (same_color_b c last x))
            last_neigh false.
    
  





Close Scope positive.
