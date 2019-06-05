From VFA Require Import Color.
(* Require Import Color. *)
From VFA Require Import Perm.
From VFA Require Import my_New_Coloring.

(** * My Coloring *)

Definition colors_available := M.t S.t.

Definition coloring_state := prod Coloring colors_available.

Definition coloring_of_state (c_s: coloring_state) : Coloring :=
  fst c_s.

Definition c_a_of_state (c_s: coloring_state) : colors_available :=
  snd c_s.

Function make_state (c : Coloring) (c_a: colors_available) : coloring_state :=
  pair c c_a.


Definition low_deg (K: nat) (n: node) (adj: nodeset) : bool := S.cardinal adj <? K.

Definition uncolored (f: Coloring) (n: node) (adj: nodeset) : bool := match M.find n f with Some c => true | None => false end.

(* Choose any uncolored vertex *)
Function get_next (g: graph) (f: coloring) : option node :=
  S.choose (subset_nodes (uncolored f) g).
(* 
Proof. ?
Defined.
*)


Definition nodes' (g: graph) := Mdomain g.

Function make_full_colors_available (g: graph) (palette: S.t) : colors_available :=
  M.fold (fun n _ m => M.add n palette m) g (M.empty S.t).


Function get_colors_av_of_vertex (n: node) (c_a: colors_available) : S.t :=
  match M.find n c_a with
    | Some c => c
    | None => S.empty
  end.

(*
Fuction unfold_option_state (c_s: coloring_state) : coloring_state  :=
  match c_s with 
    | Some a => a
    | None => pair M.Empty M.Empty
  end. *)


Definition delete_color_from_neighbors(g: graph) (c_s: coloring_state) (n: node) : coloring_state :=
  match M.find n (coloring_of_state c_s) with
    | Some cur_color => 
        S.fold 
          (fun vertex c_s_now  => 
                    match M.find vertex (c_a_of_state c_s_now) with
                      | Some colorset => pair (coloring_of_state c_s_now) (M.add vertex (S.remove cur_color colorset) (c_a_of_state c_s_now))
                      | None => pair (coloring_of_state c_s_now) (c_a_of_state c_s_now)
                    end
          )
          (adj g n) c_s
    | None => make_state (M.empty _) (M.empty _)
  end.


Definition delete_color_from_neighbors'(g: graph) (c_a: colors_available) (n: node) 
                                  (cur_color: node): colors_available :=
  S.fold 
    (fun vertex colors_now  => 
              match M.find vertex colors_now with
                | Some colorset => M.add vertex (S.remove cur_color colorset) colors_now
                | None => colors_now
              end
    )
    (adj g n) c_a.


Definition every_adj_of_node_has_available_colors (g:graph) (n:node) (c_a: colors_available) : bool :=
  S.fold 
  (fun n flag => if length (S.elements ( get_colors_av_of_vertex n c_a) ) =? 0 
    then false 
    else flag 
  )
  (adj g n) true.

Definition every_adj_of_node_has_available_colors' (g:graph) (n:node) (c_s: coloring_state) : bool :=
  S.fold 
  (fun n flag => if length (S.elements ( get_colors_av_of_vertex n (c_a_of_state c_s) ) ) =? 0 
    then false 
    else flag 
  )
  (adj g n) true.

Definition list_of_adj_of_node_with_one_color_available (g:graph) (n: node) (c_a: colors_available) : list node :=
  S.fold 
  (fun n array => if length (S.elements ( get_colors_av_of_vertex n c_a) ) =? 1 
    then n:: array 
    else array
  )
  (adj g n) [].

Definition list_of_adj_of_node_with_one_color_available' (g:graph) (n: node) (c_s: coloring_state) : list node :=
  S.fold 
  (fun n array => if length (S.elements ( get_colors_av_of_vertex n (c_a_of_state c_s) ) ) =? 1 
    then n:: array 
    else array
  )
  (adj g n) [].

(*
Function color_vertices_with_one_color_available (g: graph) (n:node) (c_a: colors_available) ()
*)
(*
process_updated_colors_available: if not every_vertex_has_available_colors return None, else Some coloring_state.
*)
(*
Function process_updated_colors_available (g:graph) (n:node) (c: coloring) (c_a: colors_available) : option coloring_state:=
  if every_adj_of_node_has_available_colors =? false 
    then None
    else fold (fun node ) (list_of_adj_of_node_with_one_color_available g n c_a) (pair c c_a).

process_just_colored_bfs: 
*)

Fixpoint process_just_colored_bfs' (dummy : nat) (n: node) (g: graph) (c_s : coloring_state) : option coloring_state :=  
  match dummy with
  | 0 => None
  | S p =>
      match every_adj_of_node_has_available_colors' g n (delete_color_from_neighbors g c_s n) with
      | false => None
      | true => 
          fold_right 
            (fun next_vertice cur_c_s => 
                  match cur_c_s with
                    | None => None
                    | Some c_s_ => process_just_colored_bfs' p next_vertice g c_s_
                  end
            ) (Some c_s) (list_of_adj_of_node_with_one_color_available' g n c_s)
      end
  end.

(*! FIXME: set dummy parameter to a provably safe value. *)

Function process_just_colored_bfs (n: node) (g: graph) (c_s : coloring_state) : option coloring_state :=
  process_just_colored_bfs' 100 n g c_s.



(* ################################################################# *)
(** * Proof of Correctness of the Algorithm. *)

(** We want to show that any coloring produced by the [color] function actually
  respects the interference constraints.  This property is called [coloring_ok].  
*)

Definition coloring_ok (palette: S.t) (g: graph) (f: coloring) :=
 forall i j, S.In j (adj g i) -> 
     (forall ci, M.find i f = Some ci -> S.In ci palette) /\
     (forall ci cj, M.find i f = Some ci -> M.find j f = Some cj -> ci<>cj).

(** **** Exercise: 2 stars (adj_ext)  *)
Lemma adj_ext: forall g i j, E.eq i j -> S.eq (adj g i) (adj g j).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (in_colors_of_1)  *)
Lemma in_colors_of_1:
  forall i s f c, S.In i s -> M.find i f = Some c -> S.In c (colors_of f s).
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars (color_correct)  *)
Theorem color_correct:
  forall palette g, 
       no_selfloop g -> 
       undirected g -> 
       coloring_ok palette g (color palette g).
(* FILL IN HERE *) Admitted.
(** [] *)

(** That concludes the proof that the algorithm is correct. *)


(* ################################################################# *)
(** * Trying Out the Algorithm on an Actual Test Case *)

Local Open Scope positive.
(* now 1,2,3, etc. are notation for [positive] numbers. *)
(* Let's use only three colors *)
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

(* ################################################################# *)
(** * Trying Out the My_Coloring  *)

Definition palette4: S.t := fold_right S.add S.empty [1; 2; 3; 4].


Definition G' := 
    mk_graph [ (1, 2) ; (2, 3); (1, 3)].

Compute (S.elements (Mdomain G')). (* = [2; 1; 3] *)

Compute (M.elements (color palette G')).

Definition full_colors4_3 := make_full_colors_available G' palette4.

Check full_colors4_3.

Compute match (M.find 3 full_colors4_3) with Some c => (S.elements c) | None => nil end.
(* = [4; 2; 1; 3] -- colors available for vertex 3 in full_colors4_3 *)

Definition delete_color1_from2_3 := delete_color_from_neighbors' G' full_colors4_3 1 1.
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

