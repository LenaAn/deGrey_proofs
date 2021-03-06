From VFA Require Import Perm.
From VFA Require Import Color.

Open Scope positive.

(*
Definition add_edge (e: (E.t*E.t)) (g: graph) : graph :=
 M.add (fst e) (S.add (snd e) (adj g (fst e))) 
  (M.add (snd e) (S.add (fst e) (adj g (snd e))) g).
*)
Definition add_edges (el: list (E.t*E.t)) (g: graph) : graph :=
  fold_right add_edge g el.

Definition mk_graph (el: list (E.t*E.t)) :=
  fold_right add_edge (M.empty _) el.

Definition G := 
    mk_graph [ (5,6); (6,2); (5,2); (1,5); (1,2); (2,4); (1,4)].

Compute (S.elements (Mdomain G)). (* = [4; 2; 6; 1; 5] *)


Definition K3 := 
    mk_graph [ (1, 2) ; (2, 3); (1, 3)].

Compute (S.elements (Mdomain K3)).

Fixpoint l_rng' (l : list node) (cur_min: node) (cur_max: node) : node * node :=
  match l with
  | nil => (cur_min, cur_max)
  | x :: xs  => let cur_min := if x <? cur_min then x else cur_min in
                let cur_max := if cur_max <? x then x else cur_max in
                l_rng' (xs) (cur_min) (cur_max)
  end.

Function l_rng (l : list node) :=
  match l with
    | nil => (1%positive, 2%positive)
    | x::xs =>  l_rng' l  x x
  end.

Function gr_rng (g : graph) : node * node :=
  l_rng (S.elements (Mdomain g)).

Compute gr_rng G.

Check M.add.

Definition rename_node (old : node) (new : node) (g : graph) : graph :=
  let nigh := adj g old in
  S.fold (fun n g' => add_edge (new, n) g') nigh (remove_node old g).

Function gr_show (g : graph) : list (node * node) :=
  S.fold (fun n l => (map (fun y => (n, y)) (S.elements (adj g n))) ++ l) (Mdomain g) nil.


Compute gr_show K3.

Compute gr_show (rename_node 3 1 (rename_node 2 7 (rename_node 1 5 K3))).
Compute S.elements (Mdomain (rename_node 3 1 (rename_node 2 7 (rename_node 1 5 K3)))).

(* The user should avoid any collision of the new and old names. *)
Function rename_all (f : node -> node) (g : graph) : graph :=
  S.fold (fun n g' => rename_node n (f n) g') (Mdomain g) g.

Compute K3.
Compute gr_show (rename_all (fun x => x * 4) K3).

(* Connect two graphs by an articulation point (aka "sharnir").
  That point MUST be present in both graphs. *)

Compute gr_rng K3.

(* Deletes one instance, if it's present, otherwise doesn't change the list *)
Fixpoint delete_from_list (l: list node) (n: node) : list node :=
  match l with
    | nil => nil
    | h::xs => if h =? n
                then xs
                else h::(delete_from_list xs n)
  end.

Compute delete_from_list [4; 3; 1; 2; 5] 6.

(* n == len(before) *)
Fixpoint sort (n: nat) (before: list node) (after: list node) : list node :=
  match n with
    | O => after
    | S n' =>
        let min_value := fst (l_rng before) in 
        let before' := delete_from_list before min_value in 
        sort n' before' ( after ++ [min_value] )
  end.


Definition rename_in_order (g: graph) : graph :=
  let sorted_vertices := sort (length (S.elements (Mdomain g))) (S.elements (Mdomain g)) nil in 
  fst ( fold_left
        (fun pair_g_next n  => 
          let next_node := snd pair_g_next in
          let g' := fst pair_g_next in
          (
            rename_node n next_node g', 
            next_node+1 
          )
        )
        sorted_vertices (g, 1) 
      ).


Definition mk_art (g1 g2 : graph) (n m : node) : graph :=
  let g2' := rename_all (fun x => x + snd(gr_rng g1)) g2 in
  let m' := m + snd(gr_rng g1) in
  let g := S.fold (fun m g' => M.add m (adj g2' m) g') (Mdomain g2') g1 in
  rename_node m' n g.

Compute gr_show (mk_art K3 K3 1 2).
Compute S.elements (Mdomain (mk_art K3 K3 1 1)).


Definition delete_edge (g: graph) (a b : node) : graph :=
  let a_neigh := S.remove b (adj g a) in
  let b_neigh := S.remove a (adj g b) in
  M.add b b_neigh (M.add a a_neigh g).


Definition mk_cmn_edge (g1 g2 : graph) (a b n m : node) : graph :=
(* Make graphs disjoint. *)
  let g2' := rename_all (fun x => x + snd (gr_rng g1)) g2 in
(* New names for the edge's vertices. *)
  let n' := n + snd (gr_rng g1) in
  let m' := m + snd (gr_rng g1) in
 (* Delete adge from second graph *)
  let g2' := delete_edge g2' n' m' in
  let g_result :=  S.fold (fun m g' => M.add m (adj g2' m) g') (Mdomain g2') g1 in
  let g_result := rename_node n' a g_result in 
  rename_node m' b g_result.

(* articulation by 2 non adjacent points in one graph to build J *)

Compute gr_show (mk_cmn_edge K3 K3 1 3 1 3).
Compute gr_show (rename_in_order (mk_cmn_edge K3 K3 1 3 1 3)).


(* Make graph H. *)
Definition H : graph := 
  let g1 := rename_in_order (mk_cmn_edge K3 K3 1 3 1 3) in
  let g2 := rename_in_order (mk_cmn_edge g1 K3 1 (snd (gr_rng g1)) 1 3) in
  let g3 := rename_in_order (mk_cmn_edge g2 K3 1 (snd (gr_rng g2)) 1 3) in
  let g4 := rename_in_order (mk_cmn_edge g3 K3 1 (snd (gr_rng g3)) 1 3) in
  rename_in_order (add_edge (2, snd (gr_rng g4)) g4).

Compute gr_show H.


Definition J: graph :=
  let HH := mk_cmn_edge H H 2 3 6 7 in
  let HH_H := mk_cmn_edge HH H 7 2 6 7 in
  let HHH := rename_node 14 12 HH_H in
  let HHH_H := mk_cmn_edge HHH H 6 7 6 7 in
  let HHHH := rename_node 19 17 HHH_H in
  let HHHH_H := mk_cmn_edge HHHH H 5 6 6 7 in
  let HHHHH := rename_node 24 22 HHHH_H in
  let HHHHH_H := mk_cmn_edge HHHHH H 4 5 6 7 in
  let HHHHHH := rename_node 29 27 HHHHH_H in
  let HHHHHH_H := mk_cmn_edge HHHHHH H 3 4 6 7 in
  let HHHHHHH :=  rename_node 34 32 HHHHHH_H in
  rename_in_order (rename_node 37 9 HHHHHHH).


(* Centers: 1, 8, 13, 17, 21, 25, 29 *)
(* Linking vertices: 9, 12, 16, 20, 24, 28 *)

Compute gr_show J.


Definition K: graph :=
  let JJ := mk_art J J 1 1 in
  let JJ := add_edges [(9, 9+31); (12, 12+31); (16, 16+31); (20, 20+31);
              (24, 24+31); (28, 28+31)] JJ in
  rename_in_order JJ.

Compute gr_show K.


Definition A := 9.
Definition B := 20.

Definition L: graph :=
  let KK := mk_art K K A A in
  let KK := add_edge (B, B+snd(gr_rng K)) KK in
  rename_in_order KK.

Compute gr_show L.


Close Scope positive.