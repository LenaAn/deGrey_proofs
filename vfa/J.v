(*Add LoadPath "/Users/lena/MIPT/\u0434\u0438\u043f\u043b\u043e\u043c/vfa" as VFA.

Print LoadPath. *)

From VFA Require Import Perm.
From VFA Require Import Color.
From VFA Require Import myGraphs.

Open Scope positive.

Print J.

(* vm_compute is faster *)
Definition gr_H := Eval vm_compute in (gr_show HHH_H).
Print gr_H.

Definition gr_H' := Eval compute in (gr_show HHH_H).
Print gr_H'.

(* Works ~ 20 min *)
Definition gr_J := Eval vm_compute in (gr_show J).


Print gr_J.

Definition J' := Eval vm_compute in (add_edges gr_J (M.empty _) ).
Print J'.

Definition mk_art' (g1 g2 : graph) (n : node) : graph :=
  let g2' := rename_all (fun x => x + snd(gr_rng g1)) g2 in
  let n' := n + snd(gr_rng g1) in
  let g := S.fold (fun m g' => M.add m (adj g2' m) g') (Mdomain g2') g1 in
  let g := rename_node n' n g in
  rename_in_order g.

Fixpoint l_rng' (l : list node) (cur_min: node) (cur_max: node)  : node * node :=
  match l with
  | nil => (cur_min, cur_max)
  | x :: xs  => let cur_min := if x <? cur_min then x else cur_min in
                let cur_max := if cur_max <? x then x else cur_max in
                l_rng' (xs) (cur_min) (cur_max)
  end.

Function gr_rng' (g : graph) : node * node :=
  l_rng' (S.elements (Mdomain g)) 1 1.

Definition max_value := Eval vm_compute in (snd(gr_rng' J')).
Print max_value.

Definition J2' := 
  Eval vm_compute in (
  let max_value := snd(gr_rng' J') in
  (rename_all (fun x => x + max_value) J')
).

Compute (gr_show J2').

Definition JJ := mk_art' J' J' 1.
Eval vm_compute in (gr_show JJ).

Definition K: graph :=
  let JJ := mk_art J' J' 1 in
  rename_in_order (add_edges [(9, 9+31); (12, 12+31); 
                                (16, 16+31); (20, 20+31);
                                  (24, 24+31); (28, 28+31)] JJ).


Definition gr_K := Eval vm_compute in (gr_show K).
(* more than 30 mins *)


Close Scope positive.