From VFA Require Import Color.

Require Import List.
Require Import FSets.    (* Efficient functional sets *)
Require Import FMaps.  (* Efficient functional maps *)
From VFA Require Import Perm.   (* to use <? notation and [bdestruct] tactic *)
Require Import Recdef.  (* Must import this to use the [Function] feature *)

Check S.In.
Search  S.In.

Definition is_clique (g: graph) :=
  forall i j, S.In j (adj g i).

Definition is_triangle (g: graph) :=
  length (S.elements (Mdomain g)) = 3 /\ is_clique g.

Definition node_is_in_graph (i: node) (g:graph) :=
  S.In i (Mdomain g).

Local Open Scope positive.


Definition G_12_undir :=
 mk_graph [(1, 2); (2, 1)].

Definition G_12 :=
 mk_graph [(1, 2)].

Definition G_12_3 :=
 mk_graph [(1, 2); (2, 3)].

Definition Triangle123 := 
    mk_graph [ (1, 2); (2, 3); (3, 1) ].

Compute node_is_in_graph 1 G_12.
Compute node_is_in_graph 5 G_12_3.

Compute M.find 1 G_12.
Check adj G_12_3 1.

(* TODO 
Example  adj G_12_3 1 = mknodset?.
S.elt \u0440\u0430\u0437\u0440\u0435\u0448\u0438\u043c\u044b\u0439?
\u043f\u0440\u043e\u0440\u0435\u0448\u0430\u0442\u044c Color.v
\u0412 \u043f\u0435\u0440\u0432\u043e\u043c \u0442\u043e\u043c\u0435 \u043f\u0440\u043e\u0447\u0438\u0442\u0430\u0442\u044c \u0447\u0430\u0441\u0442\u0438\u0447\u043d\u044b\u0435 \u0444\u0443\u043d\u043a\u0446\u0438\u0438.
\u041c\u043e\u0436\u043d\u043e \u043b\u0438 S.In \u0432\u044b\u0447\u0438\u0441\u043b\u044f\u0442\u044c?
*)


Check M.find.

Compute M.find 2 G_12.
Compute M.find 2 G_12_3.

Compute adj G_12_3 1.
Compute adj G_12 1.

Compute adj G_12_3 2.
Compute adj G_12 2.

Compute G_12_3 = G_12.

(* \u041a\u0430\u043a \u043f\u0440\u043e\u0432\u0435\u0440\u0438\u0442\u044c, \u043e\u043d\u0438 \u043e\u0434\u0438\u043d\u0430\u043a\u043e\u0432\u044b\u0435? \u0413\u0434\u0435 \u0440\u0435\u0431\u0440\u0430? *)


Theorem directed_triangle: is_clique G_12.
Proof.
  unfold is_clique. intros. unfold G_12. simpl. exact 1.


 compute.
  
  destruct (is_clique G_12). destruct G_12. simpl. intros. omega. apply H. left. destruct Triangle123.
  - 


Theorem directed_triangle: undirected Triangle123 -> False.
Proof.
  intros. destruct Triangle123.
  - 

