From VFA Require Import Color.
From VFA Require Import Perm.

Open Scope positive.

Definition palette: S.t := fold_right S.add S.empty [1; 2; 3].

Definition add_edge (e: (E.t*E.t)) (g: graph) : graph :=
 M.add (fst e) (S.add (snd e) (adj g (fst e))) 
  (M.add (snd e) (S.add (fst e) (adj g (snd e))) g).

Definition mk_graph (el: list (E.t*E.t)) :=
  fold_right add_edge (M.empty _) el.

Definition G := 
    mk_graph [ (5,6); (6,2); (5,2); (1,5); (1,2); (2,4); (1,4)].

Compute (S.elements (Mdomain G)). (* = [4; 2; 6; 1; 5] *)

Compute (M.elements (color palette G)). (* = [(4, 1); (2, 3); (6, 2); (1, 2); (5, 1)] *)

(** That is our graph coloring:  Node [4] is colored with color [1], node [2] with color [3],
  nodes [6] and [1] with [2], and node [5] with color [1]. *)


Definition palette4: S.t := fold_right S.add S.empty [1; 2; 3; 4].


Definition K3 := 
    mk_graph [ (1, 2) ; (2, 3); (1, 3)].

Compute (S.elements (Mdomain K3)). 

Compute (M.elements (color palette K3)).

Compute S.min_elt (Mdomain K3).
Compute 1%positive <? 2%positive.

Fixpoint l_rng (l : list node) : node * node :=
  match l with
  | nil => (2%positive, 1%positive)
  | x :: xs  => match xs with
                | nil => (x, x)
                | _ :: _ => let m' := fst (l_rng xs) in
                            let M' := snd (l_rng xs) in
                            let m := if x <? m' then x else m' in 
                            let M := if M' <? x then x else M' in 
                            (m, M)
               end
  end.

Function gr_rng (g : graph) : node * node :=
  l_rng (S.elements (Mdomain g)).

Compute gr_rng G.

Check M.add.

Function rename_node (old : node) (new : node) (g : graph) : graph :=
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

Check S.remove.

Compute gr_rng K3.

Function mk_art (g1 g2 : graph) (n : node) : graph :=
(* Make graphs disjoint. *)
  let g2' := rename_all (fun x => x + snd (gr_rng g1)) g2 in
(* New name for the art. point. *)
  let n' := n + snd (gr_rng g1) in
(* Remember that point's neighborhood. *)
  let nigh := adj g2' n' in
(* Remove the new copy of the art. point (with edges). *)
  let g2'' := remove_node n' g2' in
(* Join both pieces. *)
  let g := S.fold (fun m g' => M.add m (adj g2'' m) g') (Mdomain g2'') g1 in
(* Restore the edges from the art. point. *)
  S.fold (fun m g' => add_edge (n, m) g') nigh g.

Compute gr_show (mk_art K3 K3 3).
Compute S.elements (Mdomain (mk_art K3 K3 3)).

(* Connect two graphs by identifying two edges. *)

Function mk_cmn_edge (g1 g2 : graph) (a b n m : node) : graph :=
(* Make graphs disjoint. *)
  let g2' := rename_all (fun x => x + snd (gr_rng g1)) g2 in
(* New names for the edge's vertices. *)
  let n' := n + snd (gr_rng g1) in
  let m' := m + snd (gr_rng g1) in
(* Remember the neighborhoods but removing edge n'm'. *)
  let nigh_n := S.remove m' (adj g2' n') in
  let nigh_m := S.remove n' (adj g2' m') in
(* Remove the new copys of n and m. *)
  let g2'' := remove_node m' (remove_node n' g2') in
(* Join both pieces. *)
  let g := S.fold (fun k g' => M.add k (adj g2'' k) g') (Mdomain g2'') g1 in
(* Restore the edges from n and m. *)
  S.fold (fun k g' => add_edge (b, k) g') nigh_m
    (S.fold (fun k g' => add_edge (a, k) g') nigh_n g).

(*doesn't add self-loops and preserves symmetry *)

(* articulation by 2 non adjacent points in one graph to build J *)

Compute gr_show (mk_cmn_edge K3 K3 1 3 1 3).


(* Make graph H. *)
Definition H : graph := 
  let g1 := (mk_cmn_edge K3 K3 1 3 1 3) in
  let g2 := (mk_cmn_edge g1 K3 1 (snd (gr_rng g1)) 1 3) in
  let g3 := (mk_cmn_edge g2 K3 1 (snd (gr_rng g2)) 1 3) in
  let g4 := (mk_cmn_edge g3 K3 1 (snd (gr_rng g3)) 1 3) in
  add_edge (2, snd (gr_rng g4)) g4.
(* rename H *)

Compute gr_show H.


Close Scope positive.