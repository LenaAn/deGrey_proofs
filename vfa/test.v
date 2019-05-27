From VFA Require Import myGraphs.
From VFA Require Import Color.
From VFA Require Import Perm.

Open Scope positive.

Definition graph_ok (g : graph) := 
  undirected g /\ no_selfloop g.

Definition gr_deg (g : graph) (n : node) : nat :=
  S.cardinal (adj g n).

Definition edgeb (g : graph) (n m : node) :=
  S.mem n (adj g m).

Definition edge (g : graph) (n m : node) :=
  S.In n (adj g m).

Lemma adj_M_In : forall g n m,
  S.In m (adj g n) -> M.In n g.
Proof. intros. unfold adj in H.
destruct (M.find n g) eqn: H1.
- apply M.find_2 in H1. Print M.In.
  exists n0. assumption.
- discriminate.
Qed.

Check M.fold.

(* Dual to Mdomain and nodes. *)
Definition conodes (g: graph) : nodeset := 
   M.fold (fun _ a s => S.union a s) g S.empty.
(* Let's try to avoid using this. *)

(* Of course, for an undirected graph g, nodes g = conodes g. *)
Compute S.elements (nodes H).
Compute S.elements (conodes H).

Lemma edge_sym : forall g n m, graph_ok g ->
  edge g n m -> edge g m n.
Proof.
intros. unfold graph_ok, undirected in H. destruct H as [H _].
unfold edge. apply H. assumption.
Qed.

Lemma edge_irrefl : forall g n, graph_ok g ->  ~ edge g n n.
Proof.
intros. unfold graph_ok, no_selfloop in H. destruct H as [_ H].
unfold edge. apply H.
Qed.

(* The weak vesrions independent of symmetry *)
Lemma edge_corr_1 : forall g n m, edge g n m -> S.In m (nodes g).
Proof.
intros. unfold nodes. rewrite Sin_domain.
apply adj_M_In with n. unfold edge in H. assumption.
Qed.

Lemma edge_corr_2 : forall g n m, edge g n m -> S.In n (conodes g).
Proof.
intros. unfold conodes. Search M.fold.
Admitted.
(* Let's try to avoid using this. *)


Lemma edge_corr : forall g n m, graph_ok g ->
   edge g n m -> S.In n (nodes g) /\ S.In m (nodes g).
Proof.
intros; split; [ apply edge_sym in H0 | idtac ];
[ apply edge_corr_1 with m | idtac | apply edge_corr_1 with n]; assumption.
Qed.

(* Our graphs K3, H, J, K, L are graphs indeed. *)

(* All these facts can be established by a direct computation.
  But we HAVE TO bound the qunatifiers on graph nodes.
*)

Require Export List.
Require Export Sorted.
Require Export Setoid Basics Morphisms.

Lemma K3_ok : graph_ok K3.
Proof. split.
- unfold undirected. intros. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H.
(* Here lies the truth! *)
  Ltac gr_destr h :=   apply S.elements_1 in h; compute in h;
  repeat rewrite InA_cons in h; rewrite InA_nil in h;
  repeat destruct h as [? | h]; try inversion h; subst.
  gr_destr H; gr_destr H'; reflexivity.

- unfold no_selfloop. repeat intro. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H. gr_destr H; gr_destr H';
  discriminate.
Qed.

Lemma H_ok : graph_ok H.
Proof.
split.
- unfold undirected. intros. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H.
  gr_destr H; gr_destr H';  reflexivity.
- unfold no_selfloop. repeat intro. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H. gr_destr H; gr_destr H';
  discriminate.
Qed.

(* Ltac gr_test_ok := split; [ unfold undirected | unfold no_selfloop ];
  repeat intro; remember H as H'; clear HeqH'; apply edge_corr_1 in H;
   gr_destr H; gr_destr H'; [ reflexivity | discriminate ]. *)

Lemma J_ok : graph_ok J.
Proof.
split.
- unfold undirected. intros. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H.
  gr_destr H; gr_destr H';  reflexivity.
- unfold no_selfloop. repeat intro. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H. gr_destr H; gr_destr H';
  discriminate.
Qed.

Check J_ok.

Lemma K_ok : graph_ok K.
Proof.
split.
- unfold undirected. intros. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H.
  gr_destr H; gr_destr H';  reflexivity.
- unfold no_selfloop. repeat intro. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H. gr_destr H; gr_destr H';
  discriminate.
Qed.

Lemma L_ok : graph_ok L.
Proof.
split.
- unfold undirected. intros. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H.
  gr_destr H; gr_destr H';  reflexivity.
- unfold no_selfloop. repeat intro. remember H as H'.
  clear HeqH'. apply edge_corr_1 in H. gr_destr H; gr_destr H';
  discriminate.
Qed.


Lemma add_edge_corr' : forall g x y a b,
  edge (add_edge (a, b) g) x y <-> edge g x y \/ (x = a /\ y = b) \/ (x = b /\ y = a).
Proof. intros. pattern g. remember (fun g0 : graph =>
 edge (add_edge (a, b) g0) x y <-> edge g0 x y \/ (x = a /\ y = b) \/ (x = b /\ y = a)) as P.
apply WP.map_induction; intros.
- rewrite HeqP. unfold add_edge, edge. simpl.
  rewrite M.Empty_alt in H. unfold adj. repeat rewrite H.
  repeat rewrite WF.add_o. assert (H1 : S.In x S.empty <-> False).
    { split. apply Snot_in_empty. tauto. } destruct (WP.F.eq_dec a y).
  + rewrite S.add_spec, e. rewrite H1. split; intro.
    * destruct H0; subst; tauto.
    * repeat destruct H0 as [ ? | H0]; try contradiction;
      left; destruct H0; rewrite H0; try rewrite H2; reflexivity.
  + destruct (WP.F.eq_dec b y).
    * rewrite S.add_spec, e. rewrite H1. split; intro.
      { destruct H0; subst; tauto. }
      { repeat destruct H0 as [ ? | H0]; try contradiction;
      left; destruct H0; rewrite H0; try rewrite H2; reflexivity. }
    * rewrite H, H1. split; intro; try contradiction. repeat destruct H0 as [? | H0];
      [ assumption | destruct n0 | destruct n ]; symmetry; tauto.
- rewrite HeqP in *. clear HeqP. unfold WP.Add in H1. unfold add_edge, edge in *.
  simpl in *. unfold adj in *. repeat rewrite H1, WF.add_o in *.
  destruct (WP.F.eq_dec a y); repeat rewrite WF.add_o in *.
  + destruct (WP.F.eq_dec x0 a), (WP.F.eq_dec x0 y).
    * rewrite S.add_spec. split; intro H2; repeat destruct H2 as [? | H2].
      { repeat right. rewrite H2, <- e1, <- e2. tauto. } { tauto. }
      { tauto. } { left. destruct H2. rewrite <-H3, H2, <-e2, <-e1. reflexivity. }
      { left. destruct H2. rewrite H2. reflexivity. }
    * rewrite e0 in *. contradiction.
    * rewrite e0 in *. contradiction.
    * rewrite e0 in *. rewrite <- H. reflexivity.
  + destruct (WP.F.eq_dec b y), (WP.F.eq_dec x0 y).
    * destruct (WP.F.eq_dec x0 b).
      { rewrite S.add_spec. split; intro H2; repeat destruct H2 as [? | H2].
Admitted.


(* Monochromatic triplet in H with center. *)

Definition center (g : graph) (o : node) : Prop :=
  forall i, S.In i (nodes g) -> i <> o -> is_edge g i o.

Definition H_center (o : node) : Prop :=
  (gr_deg H o) = 6%nat.

Compute (gr_deg H 1).

Lemma H_center_iff : forall o, center H o <-> o = 1.
Proof.
split; intro.
-  unfold center in H.
-  rewrite H. reflexivity.
Qed.


Check subset_nodes.

Definition gr_deg_search (g : graph) (d : nat) : nodeset :=
  subset_nodes (fun _ a => Nat.eqb (S.cardinal a) d) g.

Compute S.elements (gr_deg_search H 0).

Fixpoint gr_deg_sort (g : graph) (maxd : nat) : list (list node) :=
  match maxd with
  | 0%nat => [S.elements (gr_deg_search g 0)]
  | S n => S.elements (gr_deg_search g maxd) :: gr_deg_sort g n
  end.

Compute gr_deg_sort H 6.


Definition node_color (clr : coloring) (n : node) (c : S.elt) :=
  M.find n clr = Some c.


Definition monochrom (g : graph) (clr : coloring) (o l m n : node) :=
  is_edge g o l /\ is_edge g o m /\ is_edge g o n /\ 
   exists c, (node_color clr l c /\ node_color clr m c /\ node_color clr n c).



Lemma H_monochrom_center : forall (plt : S.t) (clr : coloring) (o l m n : node),
  coloring_ok plt H clr -> monochrom H clr o l m n -> H_center H o.



Definition palette4: S.t := fold_right S.add S.empty [1; 2; 3; 4].

Compute (M.elements (color palette H)).


Close Scope positive.


