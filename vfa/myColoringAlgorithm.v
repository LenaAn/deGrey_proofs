From VFA Require Import Color.
From VFA Require Import Perm.
From VFA Require Import my_New_Coloring.
From VFA Require Import myGraphs.


(** * My Coloring *)

Definition colors_available := positive ->  S.t.

Definition low_deg (K: nat) (n: node) (adj: nodeset) : bool := S.cardinal adj <? K.

Definition uncolored (f: coloring) (n: node) (adj: nodeset) : bool := 
  match M.find n f with
    | Some c => true 
    | None => false 
  end.

(* Choose any uncolored vertex *)
Function get_next (g: graph) (f: coloring) : option node :=
  S.choose (subset_nodes (uncolored f) g).

Definition make_full_colors_available (g: graph) (palette: S.t) : colors_available :=
  fun _ => palette.

Definition empty_colors_available (g: graph) : colors_available :=
  fun _ => S.empty.

Open Scope positive.

Definition c_a_update (c_a : colors_available) (n : node) (s : S.t) :=
  fun x' => if n =? x' then s else c_a x'.

Definition delete_color_from_neighbors(g: graph) (c_a: colors_available) (clr: Coloring) (n: node):
    colors_available :=
  let color_n := clr n in
  S.fold (fun ver c_a_cur => 
              let old_colorset := c_a_cur ver in
              let new_colorset := S.remove color_n old_colorset in
              c_a_update c_a_cur ver new_colorset
          ) (adj g n) c_a.

Close Scope positive.

Definition every_adj_of_node_has_available_colors 
  (g:graph) (n:node) (c_a: colors_available) : bool :=
    let neigh := adj g n in
    S.fold 
    (fun n flag => 
        if length (S.elements (c_a n) ) =? 0
          then false
          else flag
    )
    (adj g n) true.

Definition list_of_adj_of_node_with_one_color_available 
    (g:graph) (n: node) (c_a: colors_available) : list node :=
      let neigh := adj g n in
      S.fold 
      (fun n array => if length (S.elements (c_a n) ) =? 1
        then n:: array 
        else array
      )
      (adj g n) [].

Fixpoint process_just_colored_bfs_fun
  (dummy : nat) (n: node) (g: graph) (c_a : colors_available) (clr: Coloring) :
    ( Coloring * colors_available) :=
      match dummy with
        | 0 => (EmptyColoring 5, empty_colors_available g)
        | S dummy' =>
            let neigh := adj g n in
            let c_a_new := delete_color_from_neighbors g c_a clr n in
            let list_of_1_clr_av := list_of_adj_of_node_with_one_color_available g n c_a_new in
            if (eqb false (every_adj_of_node_has_available_colors g n c_a))
              then (EmptyColoring 5, empty_colors_available g)
              else
                  fold_right
                    (fun next_n cur_c_s =>
                      let clr_cur := fst cur_c_s in
                      let c_a_cur := snd cur_c_s in
                      let new_color := nth 0 (S.elements (c_a_cur next_n)) 1%positive in
                      let new_clr_cur := update_coloring clr_cur next_n new_color in
                      process_just_colored_bfs_fun dummy' next_n g c_a_cur new_clr_cur
                    )
                     (clr, c_a_new)
                      list_of_1_clr_av
      end.

(*! FIXME: set dummy parameter to a provably safe value. *)

Function process_just_colored_bfs (n: node) (g: graph) (c_a : colors_available) (clr: Coloring)
  : ( Coloring * colors_available)  :=
  process_just_colored_bfs_fun 100 n g c_a clr.

(* TODO: need to test *)




(* ################################################################# *)
(** * Trying Out the Algorithm on an Actual Test Case *)

Local Open Scope positive.
Definition palette4: S.t := fold_right S.add S.empty [1; 2; 3; 4].

Compute (S.elements (Mdomain K3)).

Compute (M.elements (color palette4 H)).

Definition full_colors4_3 := make_full_colors_available K3 palette4.
Compute M.elements full_colors4_3.

Compute match (M.find 3 full_colors4_3) with Some c => (S.elements c) | None => nil end.
(* = [4; 2; 1; 3] -- colors available for vertex 3 in full_colors4_3 *)

Definition delete_color1_from2_3 := delete_color_from_neighbors G' full_colors4_3 1 1.
Definition delete_color1_2_from2_3 := delete_color_from_neighbors' G' delete_color1_from2_3 1 2.
Definition delete_color1_2_3_from2_3 := delete_color_from_neighbors' G' delete_color1_2_from2_3 1 3.
Definition delete_color1_2_3_4_from2_3 := delete_color_from_neighbors' G' delete_color1_2_3_from2_3 1 4.


(*!*)
Function sfind (n : S.elt) (c_a : M.t S.t) : list S.elt :=
  match (M.find n c_a) with
  | Some c => S.elements c
  | None => nil
  end.

Compute sfind 1 delete_color1_from2_3.
Compute sfind 2 delete_color1_from2_3.
Compute sfind 3 delete_color1_from2_3.

Compute sfind 1 delete_color1_2_3_4_from2_3.
Compute sfind 2 delete_color1_2_3_4_from2_3.
Compute sfind 3 delete_color1_2_3_4_from2_3.

(*!
Compute match (M.find 1 delete_color1_from2_3) with Some c => (S.elements c) | None => nil end.
Compute match (M.find 2 delete_color1_from2_3) with Some c => (S.elements c) | None => nil end.
Compute match (M.find 3 delete_color1_from2_3) with Some c => (S.elements c) | None => nil end.


Compute match (M.find 1 delete_color1_2_3_4_from2_3) with Some c => (S.elements c) | None => nil end.
Compute match (M.find 2 delete_color1_2_3_4_from2_3) with Some c => (S.elements c) | None => nil end.
Compute match (M.find 3 delete_color1_2_3_4_from2_3) with Some c => (S.elements c) | None => nil end.
*)

Compute every_vertex_has_available_colors G' delete_color1_from2_3.
Compute every_vertex_has_available_colors G' delete_color1_2_3_4_from2_3.

Compute list_of_vertices_with_one_color_available G' delete_color1_from2_3.
Compute list_of_vertices_with_one_color_available G' delete_color1_2_3_from2_3.
Compute list_of_vertices_with_one_color_available G' delete_color1_2_3_4_from2_3.


(** That is our graph coloring:  Node [4] is colored with color [1], node [2] with color [3],
  nodes [6] and [1] with [2], and node [5] with color [1]. *)

