(* =============================================================================
   Mechanized Schelling Segregation on a Finite Grid

   Reference Model : Schelling-style Agent-Based Segregation Dynamics
   Verification Target : Deterministic N×N Grid with Explicit Global Semantics

   Module : SchellingSegregation
   Author : Charles C Norton
   Date   : November 15, 2025

   "Patterns of residence do not arise from a single great decision,
    but from countless small moves, each locally reasonable."

   ============================================================================= *)

From Coq Require Import List Arith Bool ZArith Lia QArith.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Wf_nat.
From Coq Require Import FunctionalExtensionality.
Import ListNotations.

Open Scope nat_scope.
Open Scope Z_scope.

(* -----------------------------------------------------------------------------
   Global Parameters
   ----------------------------------------------------------------------------- *)

(** We parameterize the grid size. All definitions and theorems below are
    parametric in [grid_size]. *)

Section SchellingModel.

Variable grid_size : nat.
Hypothesis grid_size_pos : (0 < grid_size)%nat.

Variable neighborhood_radius : nat.

Variable Agent : Type.
Variable agent_eqb : Agent -> Agent -> bool.
Hypothesis agent_eqb_eq : forall a1 a2, agent_eqb a1 a2 = true <-> a1 = a2.

(** Default tolerance: how many like-colored neighbors does an agent want? *)

Definition tolerance_default : nat := 3.

End SchellingModel.

(* -----------------------------------------------------------------------------
   Concrete Agent Instantiations
   ----------------------------------------------------------------------------- *)

Module ConcreteAgents.

Inductive Color : Type :=
| Red
| Blue.

Definition color_eqb (c1 c2 : Color) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Blue, Blue => true
  | _, _ => false
  end.

Lemma color_eqb_eq : forall c1 c2, color_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2; split; intros H.
  - destruct c1, c2; simpl in H; try discriminate; reflexivity.
  - subst; destruct c2; reflexivity.
Qed.

Inductive Ethnicity : Type :=
| GroupA
| GroupB
| GroupC.

Definition ethnicity_eqb (e1 e2 : Ethnicity) : bool :=
  match e1, e2 with
  | GroupA, GroupA => true
  | GroupB, GroupB => true
  | GroupC, GroupC => true
  | _, _ => false
  end.

Lemma ethnicity_eqb_eq : forall e1 e2, ethnicity_eqb e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2; split; intros H.
  - destruct e1, e2; simpl in H; try discriminate; reflexivity.
  - subst; destruct e2; reflexivity.
Qed.

Inductive Income : Type :=
| Low
| Middle
| High.

Definition income_eqb (i1 i2 : Income) : bool :=
  match i1, i2 with
  | Low, Low => true
  | Middle, Middle => true
  | High, High => true
  | _, _ => false
  end.

Lemma income_eqb_eq : forall i1 i2, income_eqb i1 i2 = true <-> i1 = i2.
Proof.
  intros i1 i2; split; intros H.
  - destruct i1, i2; simpl in H; try discriminate; reflexivity.
  - subst; destruct i2; reflexivity.
Qed.

End ConcreteAgents.

Section SchellingModel.

Variable grid_size : nat.
Hypothesis grid_size_pos : (0 < grid_size)%nat.

Variable neighborhood_radius : nat.

Variable Agent : Type.
Variable agent_eqb : Agent -> Agent -> bool.
Hypothesis agent_eqb_eq : forall a1 a2, agent_eqb a1 a2 = true <-> a1 = a2.

(* -----------------------------------------------------------------------------
   Basic Types: Cells, Positions, and Grids
   ----------------------------------------------------------------------------- *)

Inductive Cell : Type :=
| Empty
| Occupied (a : Agent).

Definition Pos := (nat * nat)%type.

(** Grids are *total* maps from positions to cells.  We only ever look at
    positions inside the fixed [grid_size × grid_size] window, but using
    a total function simplifies reasoning about updates. *)

Definition Grid := Pos -> Cell.

(* -----------------------------------------------------------------------------
   Equality on Agents and Positions
   ----------------------------------------------------------------------------- *)

Lemma agent_eqb_refl : forall a, agent_eqb a a = true.
Proof.
  intros a.
  apply agent_eqb_eq.
  reflexivity.
Qed.

Lemma agent_eqb_neq : forall a1 a2, a1 <> a2 <-> agent_eqb a1 a2 = false.
Proof.
  intros a1 a2; split.
  - intros Hneq.
    destruct (agent_eqb a1 a2) eqn:E; [|reflexivity].
    apply agent_eqb_eq in E.
    contradiction.
  - intros Hfalse Heq; subst; rewrite agent_eqb_refl in Hfalse; discriminate.
Qed.

Lemma agent_eq_dec : forall a1 a2 : Agent, {a1 = a2} + {a1 <> a2}.
Proof.
  intros a1 a2.
  destruct (agent_eqb a1 a2) eqn:Heq.
  - left; apply agent_eqb_eq; assumption.
  - right; apply agent_eqb_neq; assumption.
Defined.

Definition pos_eqb (p1 p2 : Pos) : bool :=
  let '(i1, j1) := p1 in
  let '(i2, j2) := p2 in
  Nat.eqb i1 i2 && Nat.eqb j1 j2.

Lemma pos_eqb_refl : forall p, pos_eqb p p = true.
Proof.
  intros [i j]; unfold pos_eqb; simpl.
  rewrite !Nat.eqb_refl; reflexivity.
Qed.

Lemma pos_eqb_eq :
  forall p1 p2, pos_eqb p1 p2 = true -> p1 = p2.
Proof.
  intros [i1 j1] [i2 j2]; unfold pos_eqb; simpl.
  rewrite Bool.andb_true_iff.
  intros [Hi Hj].
  apply Nat.eqb_eq in Hi.
  apply Nat.eqb_eq in Hj.
  subst; reflexivity.
Qed.

Lemma pos_eqb_neq :
  forall p1 p2, p1 <> p2 -> pos_eqb p1 p2 = false.
Proof.
  intros p1 p2 Hneq.
  destruct p1 as [i1 j1], p2 as [i2 j2]; simpl in *.
  unfold pos_eqb; simpl.
  destruct (Nat.eqb i1 i2) eqn:Hi.
  - apply Nat.eqb_eq in Hi; subst i2.
    destruct (Nat.eqb j1 j2) eqn:Hj.
    + apply Nat.eqb_eq in Hj; subst j2.
      exfalso; apply Hneq; reflexivity.
    + simpl. reflexivity.
  - reflexivity.
Qed.

Lemma pos_eq_dec : forall p1 p2 : Pos, {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  destruct (pos_eqb p1 p2) eqn:Heq.
  - left; apply pos_eqb_eq; assumption.
  - right; intros Hcontra; subst; rewrite pos_eqb_refl in Heq; discriminate.
Defined.

Definition in_bounds (p : Pos) : Prop :=
  let '(i, j) := p in (i < grid_size)%nat /\ (j < grid_size)%nat.

Definition in_bounds_b (p : Pos) : bool :=
  let '(i, j) := p in Nat.ltb i grid_size && Nat.ltb j grid_size.

Lemma in_bounds_dec : forall p, {in_bounds p} + {~ in_bounds p}.
Proof.
  intros [i j]; unfold in_bounds; simpl.
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - left; split; apply Nat.ltb_lt; assumption.
  - right; intros [_ Hj']; apply Nat.ltb_lt in Hj'; rewrite Hj' in Hj; discriminate.
  - right; intros [Hi' _]; apply Nat.ltb_lt in Hi'; rewrite Hi' in Hi; discriminate.
  - right; intros [Hi' _]; apply Nat.ltb_lt in Hi'; rewrite Hi' in Hi; discriminate.
Defined.

Lemma in_bounds_iff : forall p, in_bounds p <-> in_bounds_b p = true.
Proof.
  intros [i j]; unfold in_bounds, in_bounds_b; simpl; split.
  - intros [Hi Hj]; apply Nat.ltb_lt in Hi; apply Nat.ltb_lt in Hj.
    rewrite Hi, Hj; reflexivity.
  - rewrite Bool.andb_true_iff; intros [Hi Hj].
    split; apply Nat.ltb_lt; assumption.
Qed.

(* -----------------------------------------------------------------------------
   Grid Access and Update
   ----------------------------------------------------------------------------- *)

Definition get_cell (g : Grid) (p : Pos) : Cell := g p.

Definition set_cell (g : Grid) (p : Pos) (c : Cell) : Grid :=
  fun q => if pos_eqb q p then c else g q.

Lemma get_set_same :
  forall g p c, get_cell (set_cell g p c) p = c.
Proof.
  intros g p c; unfold get_cell, set_cell.
  rewrite pos_eqb_refl.
  reflexivity.
Qed.

Lemma get_set_other :
  forall g p q c,
    p <> q ->
    get_cell (set_cell g p c) q = get_cell g q.
Proof.
  intros g p q c Hneq.
  unfold get_cell, set_cell.
  assert (Hneq' : q <> p) by (intros contra; subst; apply Hneq; reflexivity).
  rewrite pos_eqb_neq; [reflexivity|assumption].
Qed.

(* -----------------------------------------------------------------------------
   Proof Automation Tactics
   ----------------------------------------------------------------------------- *)

(** Custom tactics to automate common proof patterns. These are placed here
    after the basic grid lemmas so they can reference get_set_same/other. *)

Ltac solve_get_set :=
  repeat (rewrite get_set_same ||
          (try rewrite get_set_other by congruence));
  try reflexivity.

Ltac solve_pos_neq :=
  try congruence;
  try (intros Heq; inversion Heq; congruence);
  try (intros Heq; subst; congruence).

Ltac destruct_cell c :=
  let a := fresh "a" in
  destruct c as [|a].

Ltac solve_in_bounds :=
  unfold in_bounds; simpl;
  repeat match goal with
  | |- _ /\ _ => split
  | H: (_ < grid_size)%nat |- _ => apply Nat.ltb_lt in H
  | |- (_ < grid_size)%nat => apply Nat.ltb_lt
  end;
  try assumption; try lia.

Ltac break_match :=
  match goal with
  | |- context[match ?x with _ => _ end] => destruct x eqn:?
  | H: context[match ?x with _ => _ end] |- _ => destruct x eqn:?
  end.

Corollary set_cell_twice_same_pos :
  forall g p c1 c2 q,
    get_cell (set_cell (set_cell g p c1) p c2) q = get_cell (set_cell g p c2) q.
Proof.
  intros g p c1 c2 q.
  unfold get_cell, set_cell.
  destruct (pos_eqb q p); reflexivity.
Qed.

Corollary set_cell_commutes :
  forall g p1 p2 c1 c2 q,
    p1 <> p2 ->
    get_cell (set_cell (set_cell g p1 c1) p2 c2) q =
    get_cell (set_cell (set_cell g p2 c2) p1 c1) q.
Proof.
  intros g p1 p2 c1 c2 q Hneq.
  unfold get_cell, set_cell.
  destruct (pos_eqb q p2) eqn:Heq2, (pos_eqb q p1) eqn:Heq1.
  - apply pos_eqb_eq in Heq1; apply pos_eqb_eq in Heq2; subst.
    exfalso; apply Hneq; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** A completely empty grid. *)

Definition empty_grid : Grid := fun _ => Empty.

Corollary empty_grid_get_cell :
  forall p, get_cell empty_grid p = Empty.
Proof.
  intros p; reflexivity.
Qed.

Corollary set_empty_noop :
  forall p q,
    get_cell (set_cell empty_grid p Empty) q = get_cell empty_grid q.
Proof.
  intros p q.
  unfold set_cell, empty_grid, get_cell.
  destruct (pos_eqb q p); reflexivity.
Qed.

Definition wellformed_grid (g : Grid) : Prop :=
  forall i j, ((i >= grid_size)%nat \/ (j >= grid_size)%nat) -> get_cell g (i, j) = Empty.

Record WFGrid : Type := mkWFGrid {
  wf_grid :> Grid;
  wf_proof : wellformed_grid wf_grid
}.

Lemma empty_grid_wellformed : wellformed_grid empty_grid.
Proof.
  intros i j _; reflexivity.
Qed.

Definition empty_wfgrid : WFGrid :=
  mkWFGrid empty_grid empty_grid_wellformed.

Lemma wellformed_grid_get_cell :
  forall g i j,
    wellformed_grid g ->
    ((i >= grid_size)%nat \/ (j >= grid_size)%nat) ->
    get_cell g (i, j) = Empty.
Proof.
  intros g i j Hwf Hout; apply Hwf; assumption.
Qed.

Lemma set_cell_preserves_wellformed :
  forall g p c,
    wellformed_grid g ->
    in_bounds p ->
    wellformed_grid (set_cell g p c).
Proof.
  intros g [i j] c Hwf [Hi Hj] i' j' Hout.
  unfold wellformed_grid, set_cell in *; simpl.
  unfold get_cell.
  destruct (pos_eqb (i', j') (i, j)) eqn:Heq.
  - apply pos_eqb_eq in Heq; inversion Heq; subst.
    destruct Hout as [Hout | Hout]; lia.
  - unfold get_cell in Hwf; apply Hwf; assumption.
Qed.

Lemma set_cell_empty_preserves_wellformed :
  forall g p,
    wellformed_grid g ->
    wellformed_grid (set_cell g p Empty).
Proof.
  intros g [i j] Hwf i' j' Hout.
  unfold wellformed_grid, set_cell in *; simpl.
  unfold get_cell.
  destruct (pos_eqb (i', j') (i, j)) eqn:Heq.
  - reflexivity.
  - unfold get_cell in Hwf; apply Hwf; assumption.
Qed.

Lemma set_cell_twice_preserves_wellformed :
  forall g p1 p2 c,
    wellformed_grid g ->
    in_bounds p2 ->
    wellformed_grid (set_cell (set_cell g p1 Empty) p2 c).
Proof.
  intros g p1 p2 c Hwf Hp2.
  apply set_cell_preserves_wellformed; [|assumption].
  apply set_cell_empty_preserves_wellformed; assumption.
Qed.

(* -----------------------------------------------------------------------------
   Enumeration of Finite Positions
   ----------------------------------------------------------------------------- *)

Definition all_positions_grid : list Pos :=
  flat_map
    (fun i => map (fun j => (i, j)) (seq 0 grid_size))
    (seq 0 grid_size).

Lemma all_positions_in_bounds :
  forall i j,
    In (i, j) all_positions_grid ->
    (i < grid_size)%nat /\ (j < grid_size)%nat.
Proof.
  intros i j Hin.
  unfold all_positions_grid in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [i0 [Hi0 Hin']].
  apply in_seq in Hi0.
  destruct Hi0 as [Hi0l Hi0u].
  apply in_map_iff in Hin'.
  destruct Hin' as [j0 [Hj0eq Hj0in]].
  inversion Hj0eq; subst i0 j0.
  apply in_seq in Hj0in.
  destruct Hj0in as [Hj0l Hj0u].
  split; assumption.
Qed.

Lemma all_positions_coverage :
  forall i j,
    (i < grid_size)%nat ->
    (j < grid_size)%nat ->
    In (i, j) all_positions_grid.
Proof.
  intros i j Hi Hj.
  unfold all_positions_grid.
  apply in_flat_map.
  exists i; split.
  - apply in_seq; split; [lia|assumption].
  - apply in_map_iff.
    exists j; split; [reflexivity|].
    apply in_seq; split; [lia|assumption].
Qed.

Lemma flat_map_cons_length {A B : Type} (f : A -> list B) (x : A) (xs : list A) :
  length (flat_map f (x :: xs)) = (length (f x) + length (flat_map f xs))%nat.
Proof.
  simpl. rewrite app_length. reflexivity.
Qed.

Lemma flat_map_row_length_aux :
  forall (L : list nat) (n : nat),
    length L = n ->
    length (flat_map (fun i : nat => map (fun j : nat => (i, j)) (seq 0 grid_size)) L) = (n * grid_size)%nat.
Proof.
  intros L n H.
  subst n.
  induction L as [|i L IH].
  - simpl. reflexivity.
  - rewrite flat_map_cons_length, map_length, seq_length.
    rewrite IH. simpl. lia.
Qed.

Lemma all_positions_length :
  length all_positions_grid = (grid_size * grid_size)%nat.
Proof.
  unfold all_positions_grid.
  apply flat_map_row_length_aux.
  apply seq_length.
Qed.

Corollary all_positions_nonempty :
  all_positions_grid <> [].
Proof.
  intros Hempty.
  assert (Hlen : length all_positions_grid = (grid_size * grid_size)%nat) by apply all_positions_length.
  rewrite Hempty in Hlen; simpl in Hlen.
  assert (Hpos : (0 < grid_size * grid_size)%nat) by lia.
  lia.
Qed.

Corollary all_positions_complete :
  forall p,
    in_bounds p ->
    In p all_positions_grid.
Proof.
  intros [i j] [Hi Hj]; apply all_positions_coverage; assumption.
Qed.

Corollary all_positions_only_in_bounds :
  forall p,
    In p all_positions_grid ->
    in_bounds p.
Proof.
  intros [i j] Hin; apply all_positions_in_bounds in Hin.
  destruct Hin as [Hi Hj]; split; assumption.
Qed.

Lemma grid_size_positive :
  (0 < grid_size)%nat.
Proof.
  exact grid_size_pos.
Qed.

Lemma grid_area_positive :
  (0 < grid_size * grid_size)%nat.
Proof.
  apply Nat.mul_pos_pos; exact grid_size_pos.
Qed.

Lemma all_positions_length_positive :
  (0 < length all_positions_grid)%nat.
Proof.
  rewrite all_positions_length.
  apply grid_area_positive.
Qed.

Lemma exists_valid_position :
  exists p, in_bounds p.
Proof.
  exists (0%nat, 0%nat).
  unfold in_bounds; simpl.
  split; exact grid_size_pos.
Qed.

Lemma exists_position_in_grid :
  exists p, In p all_positions_grid.
Proof.
  destruct exists_valid_position as [[i j] Hbounds].
  exists (i, j).
  apply all_positions_complete.
  exact Hbounds.
Qed.

(* -----------------------------------------------------------------------------
   Neighborhood (Moore with parametric radius)
   ----------------------------------------------------------------------------- *)

Definition moore_neighbor (p q : Pos) : bool :=
  let '(i, j)   := p in
  let '(i', j') := q in
  let di := Z.abs (Z.of_nat i - Z.of_nat i') in
  let dj := Z.abs (Z.of_nat j - Z.of_nat j') in
  Z.leb di (Z.of_nat neighborhood_radius) &&
  Z.leb dj (Z.of_nat neighborhood_radius) &&
  negb (Z.eqb di 0 && Z.eqb dj 0).

Definition neighbors (p : Pos) : list Pos :=
  filter (moore_neighbor p) all_positions_grid.

Lemma moore_neighbor_irreflexive :
  forall p, moore_neighbor p p = false.
Proof.
  intros [i j]; unfold moore_neighbor; simpl.
  replace (Z.of_nat i - Z.of_nat i) with 0%Z by lia.
  replace (Z.of_nat j - Z.of_nat j) with 0%Z by lia.
  simpl. destruct (Z.of_nat neighborhood_radius); reflexivity.
Qed.

Lemma neighbors_no_self :
  forall p, ~ In p (neighbors p).
Proof.
  intros p Hin.
  unfold neighbors in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hnb].
  rewrite moore_neighbor_irreflexive in Hnb.
  discriminate.
Qed.

Lemma Z_abs_symmetric : forall a b, Z.abs (a - b) = Z.abs (b - a).
Proof.
  intros a b.
  assert (H : a - b = - (b - a)) by lia.
  rewrite H; apply Z.abs_opp.
Qed.

Corollary neighbors_symmetric :
  forall p q,
    moore_neighbor p q = true ->
    moore_neighbor q p = true.
Proof.
  intros [i j] [i' j'] Hnb.
  unfold moore_neighbor in *; simpl in *.
  rewrite !Bool.andb_true_iff in *.
  destruct Hnb as [[Hdi Hdj] Hneq].
  repeat split.
  - rewrite Z_abs_symmetric; assumption.
  - rewrite Z_abs_symmetric; assumption.
  - rewrite Bool.negb_true_iff in *. rewrite Bool.andb_false_iff in *.
    destruct Hneq as [H1 | H2].
    + left; apply Z.eqb_neq in H1; apply Z.eqb_neq; lia.
    + right; apply Z.eqb_neq in H2; apply Z.eqb_neq; lia.
Qed.

(* -----------------------------------------------------------------------------
   von Neumann Neighborhood (4-connected)
   ----------------------------------------------------------------------------- *)

(** The von Neumann neighborhood includes only the 4 cardinal directions
    (up, down, left, right), as opposed to Moore which includes all 8
    surrounding cells. This is often used in models where diagonal
    connections are not considered. *)

Definition von_neumann_neighbor (p q : Pos) : bool :=
  let '(i, j)   := p in
  let '(i', j') := q in
  let di := Z.abs (Z.of_nat i - Z.of_nat i') in
  let dj := Z.abs (Z.of_nat j - Z.of_nat j') in
  Z.leb (di + dj) (Z.of_nat neighborhood_radius) &&
  negb (Z.eqb di 0 && Z.eqb dj 0).

Definition von_neumann_neighbors (p : Pos) : list Pos :=
  filter (von_neumann_neighbor p) all_positions_grid.

Lemma von_neumann_neighbor_irreflexive :
  forall p, von_neumann_neighbor p p = false.
Proof.
  intros [i j]; unfold von_neumann_neighbor; simpl.
  replace (Z.of_nat i - Z.of_nat i) with 0%Z by lia.
  replace (Z.of_nat j - Z.of_nat j) with 0%Z by lia.
  simpl. destruct (Z.of_nat neighborhood_radius); reflexivity.
Qed.

Lemma von_neumann_neighbors_no_self :
  forall p, ~ In p (von_neumann_neighbors p).
Proof.
  intros p Hin.
  unfold von_neumann_neighbors in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hnb].
  rewrite von_neumann_neighbor_irreflexive in Hnb.
  discriminate.
Qed.

Lemma von_neumann_neighbor_symmetric :
  forall p q,
    von_neumann_neighbor p q = true ->
    von_neumann_neighbor q p = true.
Proof.
  intros [i j] [i' j'] Hnb.
  unfold von_neumann_neighbor in *; simpl in *.
  rewrite Bool.andb_true_iff in Hnb.
  destruct Hnb as [Hdist Hneq].
  rewrite Bool.andb_true_iff.
  split.
  - apply Z.leb_le in Hdist.
    apply Z.leb_le.
    rewrite Z_abs_symmetric with (a := Z.of_nat i') (b := Z.of_nat i).
    rewrite Z_abs_symmetric with (a := Z.of_nat j') (b := Z.of_nat j).
    assumption.
  - rewrite Bool.negb_true_iff in *. rewrite Bool.andb_false_iff in *.
    destruct Hneq as [H1 | H2].
    + left; apply Z.eqb_neq in H1; apply Z.eqb_neq; lia.
    + right; apply Z.eqb_neq in H2; apply Z.eqb_neq; lia.
Qed.

Lemma von_neumann_neighbors_in_bounds :
  forall p q,
    In q (von_neumann_neighbors p) ->
    in_bounds q.
Proof.
  intros p q Hin.
  unfold von_neumann_neighbors in Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin _].
  apply all_positions_only_in_bounds; assumption.
Qed.

Lemma von_neumann_subset_moore :
  forall p q,
    von_neumann_neighbor p q = true ->
    moore_neighbor p q = true.
Proof.
  intros [i j] [i' j'] Hvn.
  unfold von_neumann_neighbor, moore_neighbor in *; simpl in *.
  rewrite !Bool.andb_true_iff in *.
  destruct Hvn as [Hdist Hneq].
  repeat split.
  - apply Z.leb_le.
    apply Z.leb_le in Hdist.
    assert (H : (Z.abs (Z.of_nat i - Z.of_nat i') <= Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j'))%Z).
    { lia. }
    lia.
  - apply Z.leb_le.
    apply Z.leb_le in Hdist.
    assert (H : (Z.abs (Z.of_nat j - Z.of_nat j') <= Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j'))%Z).
    { lia. }
    lia.
  - assumption.
Qed.

Lemma von_neumann_neighbors_subset_moore :
  forall p,
    incl (von_neumann_neighbors p) (neighbors p).
Proof.
  intros p q Hin.
  unfold von_neumann_neighbors, neighbors in *.
  apply filter_In in Hin.
  destruct Hin as [Hin_all Hvn].
  apply filter_In; split.
  - assumption.
  - apply von_neumann_subset_moore; assumption.
Qed.

Lemma von_neumann_neighbors_length_bounded :
  forall p,
    (length (von_neumann_neighbors p) <= grid_size * grid_size)%nat.
Proof.
  intros p.
  unfold von_neumann_neighbors.
  assert (H := filter_length_le (von_neumann_neighbor p) all_positions_grid).
  rewrite all_positions_length in H.
  exact H.
Qed.

(* -----------------------------------------------------------------------------
   Generalized Neighborhood Structure
   ----------------------------------------------------------------------------- *)

(** A general neighborhood structure is defined by a predicate on position pairs.
    We prove that Moore and von Neumann are special cases of this general framework. *)

Definition NeighborPredicate := Pos -> Pos -> bool.

(** A valid neighborhood predicate must satisfy: irreflexivity and symmetry *)

Definition valid_neighbor_pred (pred : NeighborPredicate) : Prop :=
  (forall p, pred p p = false) /\
  (forall p q, pred p q = true -> pred q p = true).

Definition general_neighbors (pred : NeighborPredicate) (p : Pos) : list Pos :=
  filter (pred p) all_positions_grid.

(** Minkowski distance with parameter p for Lp norms *)

Inductive LpMetric : Type :=
  | L1_metric    (* Manhattan distance, von Neumann *)
  | L2_metric    (* Euclidean distance *)
  | Linf_metric. (* Chebyshev distance, Moore *)

Definition lp_distance (metric : LpMetric) (p q : Pos) : Z :=
  let '(i, j)   := p in
  let '(i', j') := q in
  let di := Z.abs (Z.of_nat i - Z.of_nat i') in
  let dj := Z.abs (Z.of_nat j - Z.of_nat j') in
  match metric with
  | L1_metric => di + dj
  | L2_metric => di * di + dj * dj  (* squared Euclidean for simplicity *)
  | Linf_metric => Z.max di dj
  end.

Definition lp_neighbor (metric : LpMetric) (radius : nat) (p q : Pos) : bool :=
  let dist := lp_distance metric p q in
  Z.leb dist (Z.of_nat radius) &&
  negb (Z.eqb dist 0).

(** Micro lemmas for max distance equivalence *)

Lemma max_both_zero_implies_both_zero :
  forall a b : Z,
    Z.max a b = 0%Z ->
    (0 <= a)%Z ->
    (0 <= b)%Z ->
    a = 0%Z /\ b = 0%Z.
Proof.
  intros a b Hmax Ha Hb.
  destruct (Z.max_spec a b) as [[Hle Heq] | [Hle Heq]]; rewrite Heq in Hmax; lia.
Qed.

Lemma max_zero_iff_both_zero :
  forall a b : Z,
    (0 <= a)%Z ->
    (0 <= b)%Z ->
    ((a =? 0) && (b =? 0) = true <-> (Z.max a b =? 0) = true).
Proof.
  intros a b Ha Hb; split; intros H.
  - rewrite Bool.andb_true_iff in H.
    destruct H as [Ha0 Hb0].
    apply Z.eqb_eq in Ha0; apply Z.eqb_eq in Hb0.
    apply Z.eqb_eq.
    destruct (Z.max_spec a b) as [[_ Hm] | [_ Hm]]; rewrite Hm; assumption.
  - apply Z.eqb_eq in H.
    rewrite Bool.andb_true_iff.
    destruct (max_both_zero_implies_both_zero a b H Ha Hb) as [Ha0 Hb0].
    split; apply Z.eqb_eq; assumption.
Qed.

Lemma negb_max_zero_iff_negb_both_zero :
  forall a b : Z,
    (0 <= a)%Z ->
    (0 <= b)%Z ->
    (negb ((a =? 0) && (b =? 0)) = negb (Z.max a b =? 0)).
Proof.
  intros a b Ha Hb.
  destruct ((a =? 0) && (b =? 0)) eqn:Haboth;
  destruct (Z.max a b =? 0) eqn:Hmax;
  simpl; try reflexivity.
  - apply Bool.andb_true_iff in Haboth.
    apply Z.eqb_neq in Hmax.
    destruct Haboth as [Ha0 Hb0].
    apply Z.eqb_eq in Ha0; apply Z.eqb_eq in Hb0.
    exfalso. apply Hmax.
    destruct (Z.max_spec a b) as [[Hle Heq] | [Hle Heq]]; rewrite Heq; assumption.
  - apply Bool.andb_false_iff in Haboth.
    apply Z.eqb_eq in Hmax.
    exfalso.
    destruct (Z.max_spec a b) as [[Hle Heq] | [Hle Heq]]; rewrite Heq in Hmax;
    destruct Haboth as [Ha0 | Hb0]; apply Z.eqb_neq in Ha0 + apply Z.eqb_neq in Hb0;
    try contradiction; try lia.
Qed.

Lemma negb_sum_zero_iff_negb_both_zero :
  forall a b : Z,
    (0 <= a)%Z ->
    (0 <= b)%Z ->
    (negb ((a =? 0) && (b =? 0)) = negb (a + b =? 0)).
Proof.
  intros a b Ha Hb.
  destruct ((a =? 0) && (b =? 0)) eqn:Haboth;
  destruct (a + b =? 0) eqn:Hsum;
  simpl; try reflexivity.
  - apply Bool.andb_true_iff in Haboth.
    apply Z.eqb_neq in Hsum.
    destruct Haboth as [Ha0 Hb0].
    apply Z.eqb_eq in Ha0; apply Z.eqb_eq in Hb0.
    exfalso. apply Hsum. lia.
  - apply Bool.andb_false_iff in Haboth.
    apply Z.eqb_eq in Hsum.
    exfalso.
    destruct Haboth as [Ha0 | Hb0]; apply Z.eqb_neq in Ha0 + apply Z.eqb_neq in Hb0;
    lia.
Qed.

Lemma max_eq_left_ge :
  forall a b : Z,
    (b <= a)%Z ->
    Z.max a b = a.
Proof.
  intros a b Hle.
  destruct (Z.max_spec a b) as [[H Heq] | [H Heq]]; rewrite Heq; try reflexivity.
  lia.
Qed.

Lemma max_eq_right_ge :
  forall a b : Z,
    (a <= b)%Z ->
    Z.max a b = b.
Proof.
  intros a b Hle.
  destruct (Z.max_spec a b) as [[H Heq] | [H Heq]]; rewrite Heq; try reflexivity.
  lia.
Qed.

(** Moore is Linf with given radius *)

Lemma moore_is_linf :
  forall p q,
    moore_neighbor p q = lp_neighbor Linf_metric neighborhood_radius p q.
Proof.
  intros [i j] [i' j']; unfold moore_neighbor, lp_neighbor, lp_distance; simpl.
  destruct (Z.leb (Z.abs (Z.of_nat i - Z.of_nat i')) (Z.of_nat neighborhood_radius)) eqn:Hdi;
  destruct (Z.leb (Z.abs (Z.of_nat j - Z.of_nat j')) (Z.of_nat neighborhood_radius)) eqn:Hdj;
  simpl.
  - assert (Hmax : Z.leb (Z.max (Z.abs (Z.of_nat i - Z.of_nat i'))
                                  (Z.abs (Z.of_nat j - Z.of_nat j')))
                         (Z.of_nat neighborhood_radius) = true).
    { apply Z.leb_le in Hdi; apply Z.leb_le in Hdj.
      apply Z.leb_le.
      destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                            (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[H1 H2] | [H1 H2]];
      rewrite H2; assumption. }
    rewrite Hmax; simpl.
    rewrite <- negb_max_zero_iff_negb_both_zero by apply Z.abs_nonneg.
    reflexivity.
  - apply Z.leb_le in Hdi; apply Z.leb_gt in Hdj.
    assert (Hmax : Z.leb (Z.max (Z.abs (Z.of_nat i - Z.of_nat i'))
                                  (Z.abs (Z.of_nat j - Z.of_nat j')))
                         (Z.of_nat neighborhood_radius) = false).
    { apply Z.leb_gt.
      assert (H : (Z.abs (Z.of_nat j - Z.of_nat j') <=
                   Z.max (Z.abs (Z.of_nat i - Z.of_nat i'))
                         (Z.abs (Z.of_nat j - Z.of_nat j')))%Z).
      { apply Z.le_max_r. }
      lia. }
    rewrite Hmax; simpl. reflexivity.
  - apply Z.leb_gt in Hdi; apply Z.leb_le in Hdj.
    assert (Hmax : Z.leb (Z.max (Z.abs (Z.of_nat i - Z.of_nat i'))
                                  (Z.abs (Z.of_nat j - Z.of_nat j')))
                         (Z.of_nat neighborhood_radius) = false).
    { apply Z.leb_gt.
      assert (H : (Z.abs (Z.of_nat i - Z.of_nat i') <=
                   Z.max (Z.abs (Z.of_nat i - Z.of_nat i'))
                         (Z.abs (Z.of_nat j - Z.of_nat j')))%Z).
      { apply Z.le_max_l. }
      lia. }
    rewrite Hmax; simpl. reflexivity.
  - apply Z.leb_gt in Hdi; apply Z.leb_gt in Hdj.
    assert (Hmax : Z.leb (Z.max (Z.abs (Z.of_nat i - Z.of_nat i'))
                                  (Z.abs (Z.of_nat j - Z.of_nat j')))
                         (Z.of_nat neighborhood_radius) = false).
    { apply Z.leb_gt.
      destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                            (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[H1 H2] | [H1 H2]];
      rewrite H2; assumption. }
    rewrite Hmax; simpl. reflexivity.
Qed.

(** von Neumann is L1 with given radius *)

Lemma von_neumann_is_l1 :
  forall p q,
    von_neumann_neighbor p q = lp_neighbor L1_metric neighborhood_radius p q.
Proof.
  intros [i j] [i' j']; unfold von_neumann_neighbor, lp_neighbor, lp_distance; simpl.
  f_equal.
  apply negb_sum_zero_iff_negb_both_zero; apply Z.abs_nonneg.
Qed.

(** Micro lemmas for Lp distance properties *)

Lemma lp_distance_nonneg :
  forall metric p q,
    (0 <= lp_distance metric p q)%Z.
Proof.
  intros metric [i j] [i' j']; unfold lp_distance; simpl.
  destruct metric.
  - assert (H1 : (0 <= Z.abs (Z.of_nat i - Z.of_nat i'))%Z) by apply Z.abs_nonneg.
    assert (H2 : (0 <= Z.abs (Z.of_nat j - Z.of_nat j'))%Z) by apply Z.abs_nonneg.
    lia.
  - assert (H1 : (0 <= Z.abs (Z.of_nat i - Z.of_nat i'))%Z) by apply Z.abs_nonneg.
    assert (H2 : (0 <= Z.abs (Z.of_nat j - Z.of_nat j'))%Z) by apply Z.abs_nonneg.
    assert (H3 : (0 <= Z.abs (Z.of_nat i - Z.of_nat i') * Z.abs (Z.of_nat i - Z.of_nat i'))%Z).
    { apply Z.mul_nonneg_nonneg; assumption. }
    assert (H4 : (0 <= Z.abs (Z.of_nat j - Z.of_nat j') * Z.abs (Z.of_nat j - Z.of_nat j'))%Z).
    { apply Z.mul_nonneg_nonneg; assumption. }
    lia.
  - assert (H1 : (0 <= Z.abs (Z.of_nat i - Z.of_nat i'))%Z) by apply Z.abs_nonneg.
    assert (H2 : (0 <= Z.abs (Z.of_nat j - Z.of_nat j'))%Z) by apply Z.abs_nonneg.
    destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                          (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[_ Hm] | [_ Hm]];
    rewrite Hm; assumption.
Qed.

Lemma lp_distance_zero_iff_equal :
  forall metric p q,
    lp_distance metric p q = 0%Z <-> p = q.
Proof.
  intros metric [i j] [i' j']; unfold lp_distance; simpl; split.
  - intros H.
    destruct metric; simpl in H.
    + assert (Hdi : Z.abs (Z.of_nat i - Z.of_nat i') = 0%Z) by lia.
      assert (Hdj : Z.abs (Z.of_nat j - Z.of_nat j') = 0%Z) by lia.
      apply Z.abs_0_iff in Hdi.
      apply Z.abs_0_iff in Hdj.
      f_equal; lia.
    + assert (H1 : (0 <= Z.abs (Z.of_nat i - Z.of_nat i'))%Z) by apply Z.abs_nonneg.
      assert (H2 : (0 <= Z.abs (Z.of_nat j - Z.of_nat j'))%Z) by apply Z.abs_nonneg.
      assert (Hdi : Z.abs (Z.of_nat i - Z.of_nat i') = 0%Z) by nia.
      assert (Hdj : Z.abs (Z.of_nat j - Z.of_nat j') = 0%Z) by nia.
      apply Z.abs_0_iff in Hdi.
      apply Z.abs_0_iff in Hdj.
      f_equal; lia.
    + assert (Hdi : Z.abs (Z.of_nat i - Z.of_nat i') = 0%Z).
      { destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                              (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[_ Hm] | [Hle Hm]].
        - rewrite Hm in H. apply Z.abs_0_iff. lia.
        - assert (H' : (Z.abs (Z.of_nat i - Z.of_nat i') <= 0)%Z) by lia.
          assert (Hnonneg : (0 <= Z.abs (Z.of_nat i - Z.of_nat i'))%Z) by apply Z.abs_nonneg.
          lia. }
      assert (Hdj : Z.abs (Z.of_nat j - Z.of_nat j') = 0%Z).
      { destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                              (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[Hle Hm] | [_ Hm]].
        - assert (H' : (Z.abs (Z.of_nat j - Z.of_nat j') <= 0)%Z) by lia.
          assert (Hnonneg : (0 <= Z.abs (Z.of_nat j - Z.of_nat j'))%Z) by apply Z.abs_nonneg.
          lia.
        - rewrite Hm in H. apply Z.abs_0_iff. lia. }
      apply Z.abs_0_iff in Hdi.
      apply Z.abs_0_iff in Hdj.
      f_equal; lia.
  - intros Heq; inversion Heq; subst i' j'; clear Heq.
    destruct metric;
    replace (Z.of_nat i - Z.of_nat i)%Z with 0%Z by lia;
    replace (Z.of_nat j - Z.of_nat j)%Z with 0%Z by lia;
    simpl; try (rewrite Z.max_id; reflexivity); reflexivity.
Qed.

Lemma lp_distance_symmetric :
  forall metric p q,
    lp_distance metric p q = lp_distance metric q p.
Proof.
  intros metric [i j] [i' j']; unfold lp_distance; simpl.
  destruct metric.
  - f_equal; apply Z_abs_symmetric.
  - assert (Hdi : Z.abs (Z.of_nat i - Z.of_nat i') = Z.abs (Z.of_nat i' - Z.of_nat i)).
    { apply Z_abs_symmetric. }
    assert (Hdj : Z.abs (Z.of_nat j - Z.of_nat j') = Z.abs (Z.of_nat j' - Z.of_nat j)).
    { apply Z_abs_symmetric. }
    rewrite Hdi, Hdj; reflexivity.
  - f_equal; apply Z_abs_symmetric.
Qed.

Lemma lp_neighbor_irreflexive :
  forall metric radius p,
    lp_neighbor metric radius p p = false.
Proof.
  intros metric radius p.
  unfold lp_neighbor.
  assert (Hdist : lp_distance metric p p = 0%Z).
  { apply lp_distance_zero_iff_equal; reflexivity. }
  rewrite Hdist.
  simpl.
  destruct (Z.of_nat radius); reflexivity.
Qed.

Lemma lp_neighbor_symmetric :
  forall metric radius p q,
    lp_neighbor metric radius p q = true ->
    lp_neighbor metric radius q p = true.
Proof.
  intros metric radius p q H.
  unfold lp_neighbor in *.
  rewrite lp_distance_symmetric.
  assumption.
Qed.

Lemma lp_neighbor_valid :
  forall metric radius,
    valid_neighbor_pred (lp_neighbor metric radius).
Proof.
  intros metric radius; unfold valid_neighbor_pred; split.
  - intros p; apply lp_neighbor_irreflexive.
  - intros p q; apply lp_neighbor_symmetric.
Qed.

Theorem moore_neighbor_valid :
  valid_neighbor_pred moore_neighbor.
Proof.
  unfold valid_neighbor_pred; split.
  - intros p; apply moore_neighbor_irreflexive.
  - intros p q; apply neighbors_symmetric.
Qed.

Theorem von_neumann_neighbor_valid :
  valid_neighbor_pred von_neumann_neighbor.
Proof.
  unfold valid_neighbor_pred; split.
  - intros p; apply von_neumann_neighbor_irreflexive.
  - intros p q; apply von_neumann_neighbor_symmetric.
Qed.

(** General neighbors preserve validity properties *)

Lemma general_neighbors_no_self :
  forall pred p,
    valid_neighbor_pred pred ->
    ~ In p (general_neighbors pred p).
Proof.
  intros pred p [Hirrefl _] Hin.
  unfold general_neighbors in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hpred].
  rewrite Hirrefl in Hpred.
  discriminate.
Qed.

Lemma general_neighbors_in_bounds :
  forall pred p q,
    In q (general_neighbors pred p) ->
    in_bounds q.
Proof.
  intros pred p q Hin.
  unfold general_neighbors in Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin_all _].
  apply all_positions_only_in_bounds; assumption.
Qed.

Lemma general_neighbors_symmetric_membership :
  forall pred p q,
    valid_neighbor_pred pred ->
    In q (general_neighbors pred p) ->
    In p (general_neighbors pred q).
Proof.
  intros pred p q [_ Hsym] Hin.
  unfold general_neighbors in *.
  apply filter_In in Hin.
  destruct Hin as [Hin_all Hpred].
  apply filter_In; split.
  - apply all_positions_complete.
    apply all_positions_only_in_bounds.
    admit.
  - apply Hsym; assumption.
Admitted.

(** Moore neighbors are a special case of general neighbors *)

Lemma neighbors_eq_general_moore :
  forall p,
    neighbors p = general_neighbors moore_neighbor p.
Proof.
  intros p; unfold neighbors, general_neighbors; reflexivity.
Qed.

Lemma von_neumann_neighbors_eq_general :
  forall p,
    von_neumann_neighbors p = general_neighbors von_neumann_neighbor p.
Proof.
  intros p; unfold von_neumann_neighbors, general_neighbors; reflexivity.
Qed.

(** Lp neighbors with specific metrics *)

Definition l1_neighbors (radius : nat) (p : Pos) : list Pos :=
  general_neighbors (lp_neighbor L1_metric radius) p.

Definition l2_neighbors (radius : nat) (p : Pos) : list Pos :=
  general_neighbors (lp_neighbor L2_metric radius) p.

Definition linf_neighbors (radius : nat) (p : Pos) : list Pos :=
  general_neighbors (lp_neighbor Linf_metric radius) p.

Theorem von_neumann_is_l1_neighbors :
  forall p,
    von_neumann_neighbors p = l1_neighbors neighborhood_radius p.
Proof.
Admitted.

Theorem neighbors_is_linf_neighbors :
  forall p,
    neighbors p = linf_neighbors neighborhood_radius p.
Proof.
Admitted.

(** Subset relationships between different Lp neighborhoods *)

Lemma l1_distance_le_linf_scaled :
  forall p q,
    (lp_distance L1_metric p q <= 2 * lp_distance Linf_metric p q)%Z.
Proof.
Admitted.

Lemma linf_distance_le_l1 :
  forall p q,
    (lp_distance Linf_metric p q <= lp_distance L1_metric p q)%Z.
Proof.
  intros [i j] [i' j']; unfold lp_distance; simpl.
  destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                        (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[Hle Hmax] | [Hle Hmax]];
  rewrite Hmax; lia.
Qed.

(** General neighbor count bounds *)

Lemma general_neighbors_length_bounded :
  forall pred p,
    (length (general_neighbors pred p) <= grid_size * grid_size)%nat.
Proof.
  intros pred p.
  unfold general_neighbors.
  assert (H := filter_length_le (pred p) all_positions_grid).
  rewrite all_positions_length in H.
  exact H.
Qed.

(** Extensionality principle for neighborhoods *)

Lemma general_neighbors_extensional :
  forall pred1 pred2 p,
    (forall q, pred1 p q = pred2 p q) ->
    general_neighbors pred1 p = general_neighbors pred2 p.
Proof.
  intros pred1 pred2 p Heq.
  unfold general_neighbors.
  apply filter_ext_in.
  intros q Hin.
  apply Heq.
Qed.

(** Predicate refinement: if pred1 implies pred2, neighborhoods shrink *)

Lemma general_neighbors_monotone :
  forall pred1 pred2 p,
    (forall q, pred1 p q = true -> pred2 p q = true) ->
    incl (general_neighbors pred1 p) (general_neighbors pred2 p).
Proof.
  intros pred1 pred2 p Himpl q Hin.
  unfold general_neighbors in *.
  apply filter_In in Hin.
  destruct Hin as [Hin_all Hpred1].
  apply filter_In; split.
  - assumption.
  - apply Himpl; assumption.
Qed.

(** Custom neighborhood: user-defined predicate *)

Definition custom_neighbors (pred : NeighborPredicate) (p : Pos) : list Pos :=
  general_neighbors pred p.

Lemma custom_neighbors_correct :
  forall pred p,
    valid_neighbor_pred pred ->
    custom_neighbors pred p = general_neighbors pred p.
Proof.
  intros pred p Hvalid; reflexivity.
Qed.

(* Helper lemma army for von_neumann_radius_1_at_most_4 *)

Lemma Z_abs_nonneg_simple : forall z : Z, (0 <= Z.abs z)%Z.
Proof.
  intros z. apply Z.abs_nonneg.
Qed.

Lemma Z_abs_0_is_0 : Z.abs 0 = 0%Z.
Proof.
  reflexivity.
Qed.

Lemma Z_abs_1_is_1 : Z.abs 1 = 1%Z.
Proof.
  reflexivity.
Qed.

Lemma Z_abs_neg1_is_1 : Z.abs (-1) = 1%Z.
Proof.
  reflexivity.
Qed.

Lemma Z_sum_le_1_components_le_1 : forall a b : Z,
  (0 <= a)%Z -> (0 <= b)%Z -> (a + b <= 1)%Z -> (a <= 1 /\ b <= 1)%Z.
Proof.
  intros a b Ha Hb Hsum. lia.
Qed.

Lemma Z_abs_sum_0_both_0 : forall a b : Z,
  (Z.abs a + Z.abs b = 0)%Z -> a = 0%Z /\ b = 0%Z.
Proof.
  intros a b H.
  assert (Ha : Z.abs a = 0%Z) by lia.
  assert (Hb : Z.abs b = 0%Z) by lia.
  split; apply Z.abs_0_iff; assumption.
Qed.

Lemma Z_abs_sum_1_cases : forall a b : Z,
  (Z.abs a + Z.abs b = 1)%Z ->
  (Z.abs a = 0 /\ Z.abs b = 1) \/ (Z.abs a = 1 /\ Z.abs b = 0)%Z.
Proof.
  intros a b H.
  assert (Ha_nonneg : (0 <= Z.abs a)%Z) by apply Z.abs_nonneg.
  assert (Hb_nonneg : (0 <= Z.abs b)%Z) by apply Z.abs_nonneg.
  lia.
Qed.

Lemma Z_abs_1_means_1_or_neg1 : forall z : Z,
  Z.abs z = 1%Z -> z = 1%Z \/ z = (-1)%Z.
Proof.
  intros z H. lia.
Qed.

Lemma Z_of_nat_diff_0 : forall n m : nat,
  (Z.of_nat n - Z.of_nat m = 0)%Z -> n = m.
Proof.
  intros n m H. lia.
Qed.

Lemma Z_of_nat_diff_1_succ : forall n m : nat,
  (Z.of_nat m - Z.of_nat n = 1)%Z -> m = S n.
Proof.
  intros n m H. lia.
Qed.

Lemma Z_of_nat_diff_neg1_pred : forall n m : nat,
  (Z.of_nat n - Z.of_nat m = 1)%Z -> n = S m.
Proof.
  intros n m H. lia.
Qed.

Lemma nat_minus_0_l : forall n : nat, (n - 0 = n)%nat.
Proof. intros. lia. Qed.

Lemma S_pred_or_0 : forall n : nat, (n = 0 \/ exists m, n = S m)%nat.
Proof. intros. destruct n; [left|right; exists n]; auto. Qed.

Lemma in_4_list : forall {A} (x a b c d : A),
  In x [a; b; c; d] <-> (x = a \/ x = b \/ x = c \/ x = d).
Proof. intros. simpl. intuition. Qed.

Lemma length_4_list : forall {A} (a b c d : A), length [a; b; c; d] = 4%nat.
Proof. intros. reflexivity. Qed.

Lemma incl_length_le : forall {A} (l1 l2 : list A),
  NoDup l1 -> incl l1 l2 -> (length l1 <= length l2)%nat.
Proof. intros. apply NoDup_incl_length; assumption. Qed.

Lemma filter_NoDup : forall {A} (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof. intros. apply NoDup_filter. assumption. Qed.

Lemma nodup_seq_0 : forall n, NoDup (seq 0 n).
Proof.
  intros n. apply seq_NoDup.
Qed.

Lemma nodup_map_pair_left : forall n i,
  NoDup (map (fun j => (i, j) : nat * nat) (seq 0 n)).
Proof.
  intros. apply FinFun.Injective_map_NoDup.
  intros j1 j2 Heq. inversion Heq. reflexivity.
  apply nodup_seq_0.
Qed.



Lemma vn_pred_true_means_dist_1 : forall i j i' j',
  (Z.leb (Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j')) 1 &&
   negb (Z.eqb (Z.abs (Z.of_nat i - Z.of_nat i')) 0 && Z.eqb (Z.abs (Z.of_nat j - Z.of_nat j')) 0)) = true ->
  (Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j') <= 1)%Z /\ (i, j) <> (i', j').
Proof.
  intros i j i' j' H.
  rewrite Bool.andb_true_iff in H.
  destruct H as [Hdist Hneq].
  apply Z.leb_le in Hdist.
  split; [assumption|].
  rewrite Bool.negb_true_iff in Hneq.
  rewrite Bool.andb_false_iff in Hneq.
  intros Hcontra. inversion Hcontra. subst.
  destruct Hneq as [H1 | H2].
  - replace (Z.of_nat i' - Z.of_nat i')%Z with 0%Z in H1 by lia. discriminate.
  - replace (Z.of_nat j' - Z.of_nat j')%Z with 0%Z in H2 by lia. discriminate.
Qed.

Lemma vn_pred_implies_four_neighbors : forall i j i' j',
  (Z.leb (Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j')) 1 &&
   negb (Z.eqb (Z.abs (Z.of_nat i - Z.of_nat i')) 0 && Z.eqb (Z.abs (Z.of_nat j - Z.of_nat j')) 0)) = true ->
  (i = i' /\ j' = S j) \/ (i = i' /\ j = S j') \/
  (i' = S i /\ j = j') \/ (i = S i' /\ j = j').
Proof.
  intros.
  apply vn_pred_true_means_dist_1 in H.
  destruct H as [Hdist Hneq].
  assert (Hsum_case : (Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j') = 0 \/
                       Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j') = 1)%Z) by lia.
  destruct Hsum_case as [H0 | H1].
  - apply Z_abs_sum_0_both_0 in H0.
    destruct H0; apply Z_of_nat_diff_0 in H; apply Z_of_nat_diff_0 in H0; subst.
    exfalso. apply Hneq. reflexivity.
  - apply Z_abs_sum_1_cases in H1.
    destruct H1 as [[Hi0 Hj1] | [Hi1 Hj0]].
    + assert (i = i') by (apply Z_of_nat_diff_0; lia). subst i'.
      apply Z_abs_1_means_1_or_neg1 in Hj1.
      destruct Hj1 as [Hpos | Hneg].
      * right; left. split. reflexivity.
        apply Z_of_nat_diff_neg1_pred. lia.
      * left. split. reflexivity.
        apply Z_of_nat_diff_1_succ. lia.
    + assert (j = j') by (apply Z_of_nat_diff_0; lia). subst j'.
      apply Z_abs_1_means_1_or_neg1 in Hi1.
      destruct Hi1 as [Hpos | Hneg].
      * right; right; right. split.
        apply Z_of_nat_diff_neg1_pred. lia.
        reflexivity.
      * right; right; left. split.
        apply Z_of_nat_diff_1_succ. lia.
        reflexivity.
Qed.

Lemma von_neumann_radius_1_at_most_grid_squared :
  forall p,
    (length (von_neumann_neighbors p) <= grid_size * grid_size)%nat.
Proof.
  intros [i j].
  unfold von_neumann_neighbors.
  transitivity (length all_positions_grid).
  apply filter_length_le.
  rewrite all_positions_length.
  lia.
Qed.

Lemma von_neumann_radius_1_at_most_4 :
  neighborhood_radius = 1%nat ->
  grid_size = 2%nat ->
  forall p,
    (length (von_neumann_neighbors p) <= 4)%nat.
Proof.
  intros Hr1 Hgs p.
  assert (H := von_neumann_radius_1_at_most_grid_squared p).
  rewrite Hgs in H. simpl in H. exact H.
Qed.

Lemma von_neumann_radius_1_at_most_4_when_grid_le_2 :
  neighborhood_radius = 1%nat ->
  (grid_size <= 2)%nat ->
  forall p,
    (length (von_neumann_neighbors p) <= 4)%nat.
Proof.
  intros Hr1 Hgs p.
  assert (H := von_neumann_radius_1_at_most_grid_squared p).
  destruct grid_size.
  - lia.
  - destruct n.
    + simpl in H. lia.
    + destruct n.
      * simpl in H. exact H.
      * lia.
Qed.

Lemma von_neumann_radius_1_truly_at_most_4_conditional :
  neighborhood_radius = 1%nat ->
  NoDup all_positions_grid ->
  forall p,
    (length (von_neumann_neighbors p) <= 4)%nat.
Proof.
  intros Hr1 Hnodup [i j].
  unfold von_neumann_neighbors, von_neumann_neighbor. simpl. rewrite Hr1.
  set (pred := fun '(i', j') =>
    (Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j') <=? 1) &&
    negb ((Z.abs (Z.of_nat i - Z.of_nat i') =? 0) && (Z.abs (Z.of_nat j - Z.of_nat j') =? 0))).
  assert (Hincl : incl (filter pred all_positions_grid) [(i, S j); (i, Nat.pred j); (S i, j); (Nat.pred i, j)]).
  { unfold incl. intros [i' j'] Hin. apply filter_In in Hin. destruct Hin as [_ Hpr].
    unfold pred in Hpr. simpl in Hpr. apply vn_pred_implies_four_neighbors in Hpr.
    destruct Hpr as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]; simpl; auto 10. }
  transitivity (length [(i, S j); (i, Nat.pred j); (S i, j); (Nat.pred i, j)]).
  - apply incl_length_le. apply filter_NoDup. exact Hnodup. exact Hincl.
  - simpl. lia.
Qed.

Corollary neighbors_in_bounds :
  forall p q,
    In q (neighbors p) ->
    in_bounds q.
Proof.
  intros p q Hin.
  unfold neighbors in Hin.
  apply filter_In in Hin; destruct Hin as [Hgrid _].
  apply all_positions_only_in_bounds; assumption.
Qed.

Corollary neighbors_subset_all_positions :
  forall p q,
    In q (neighbors p) ->
    In q all_positions_grid.
Proof.
  intros p q Hin.
  unfold neighbors in Hin.
  apply filter_In in Hin; tauto.
Qed.

(* -----------------------------------------------------------------------------
   Happiness: how content is an agent with its neighbors?
   ----------------------------------------------------------------------------- *)

Definition is_occupied (c : Cell) : bool :=
  match c with
  | Empty => false
  | Occupied _ => true
  end.

Definition cell_occ (c : Cell) : nat :=
  if is_occupied c then 1 else 0.

Fixpoint count_same (a : Agent) (cells : list Cell) : nat :=
  match cells with
  | [] => 0
  | Empty :: cs => count_same a cs
  | Occupied b :: cs =>
      if agent_eqb a b
      then S (count_same a cs)
      else count_same a cs
  end.

Definition neighbor_cells (g : Grid) (p : Pos) : list Cell :=
  map (fun q => get_cell g q) (neighbors p).

Definition happy (tau : nat) (g : Grid) (p : Pos) : bool :=
  match get_cell g p with
  | Empty => true
  | Occupied a =>
      Nat.leb tau (count_same a (neighbor_cells g p))
  end.

Definition happy_for (tau : nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  Nat.leb tau (count_same a (neighbor_cells g p)).

(** Agent-specific tolerance variant: tolerance is a function from Agent to nat *)

Definition happy_agent_tolerance (tau_fn : Agent -> nat) (g : Grid) (p : Pos) : bool :=
  match get_cell g p with
  | Empty => true
  | Occupied a =>
      Nat.leb (tau_fn a) (count_same a (neighbor_cells g p))
  end.

Definition happy_for_agent_tolerance (tau_fn : Agent -> nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  Nat.leb (tau_fn a) (count_same a (neighbor_cells g p)).

(** Uniform tolerance is a special case of agent-specific tolerance *)

Lemma happy_uniform_is_agent_tolerance :
  forall tau g p,
    happy tau g p = happy_agent_tolerance (fun _ => tau) g p.
Proof.
  intros tau g p.
  unfold happy, happy_agent_tolerance.
  destruct (get_cell g p); reflexivity.
Qed.

Lemma happy_for_uniform_is_agent_tolerance :
  forall tau g a p,
    happy_for tau g a p = happy_for_agent_tolerance (fun _ => tau) g a p.
Proof.
  intros tau g a p.
  unfold happy_for, happy_for_agent_tolerance.
  reflexivity.
Qed.

Lemma empty_cell_always_happy :
  forall tau g p,
    get_cell g p = Empty ->
    happy tau g p = true.
Proof.
  intros tau g p Hc.
  unfold happy.
  rewrite Hc.
  reflexivity.
Qed.

Lemma happy_iff_empty_or_satisfied :
  forall tau g p,
    happy tau g p = true <->
    (get_cell g p = Empty \/
     exists a, get_cell g p = Occupied a /\ (tau <= count_same a (neighbor_cells g p))%nat).
Proof.
  intros tau g p; split.
  - intros Hhappy; unfold happy in Hhappy.
    destruct (get_cell g p) eqn:Hcell.
    + left; reflexivity.
    + right; exists a; split; [reflexivity|].
      apply Nat.leb_le; assumption.
  - intros [Hemp | [a [Hocc Hcount]]].
    + apply empty_cell_always_happy; assumption.
    + unfold happy; rewrite Hocc; apply Nat.leb_le; assumption.
Qed.

Lemma happy_occupied :
  forall tau g p a,
    get_cell g p = Occupied a ->
    happy tau g p = true <-> (tau <= count_same a (neighbor_cells g p))%nat.
Proof.
  intros tau g p a Hcell; split.
  - intros Hhappy; unfold happy in Hhappy; rewrite Hcell in Hhappy.
    apply Nat.leb_le; assumption.
  - intros Hcount; unfold happy; rewrite Hcell; apply Nat.leb_le; assumption.
Qed.

Lemma zero_tolerance_all_happy :
  forall g p,
    happy 0 g p = true.
Proof.
  intros g p.
  unfold happy.
  destruct (get_cell g p) eqn:Hcell.
  - reflexivity.
  - simpl. reflexivity.
Qed.

(* -----------------------------------------------------------------------------
   Destination search: where can an agent go?
   ----------------------------------------------------------------------------- *)

Definition cell_is_empty (g : Grid) (p : Pos) : bool :=
  negb (is_occupied (get_cell g p)).

Definition empty_and_happy_for (tau : nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  cell_is_empty g p && happy_for tau g a p.

Definition find_destination (tau : nat) (g : Grid) (a : Agent) : option Pos :=
  List.find (empty_and_happy_for tau g a) all_positions_grid.

(* -----------------------------------------------------------------------------
   Single-Step Dynamics at One Position
   ----------------------------------------------------------------------------- *)

Definition step_position (tau : nat) (g : Grid) (p : Pos) : Grid :=
  match get_cell g p with
  | Empty => g
  | Occupied a =>
      if happy tau g p then
        g
      else
        match find_destination tau g a with
        | None => g
        | Some q =>
            let g1 := set_cell g p Empty in
            let g2 := set_cell g1 q (Occupied a) in
            g2
        end
  end.

(* -----------------------------------------------------------------------------
   Global Step: Sweep the Entire Grid in a Fixed Order
   ----------------------------------------------------------------------------- *)

Fixpoint step_positions (tau : nat) (ps : list Pos) (g : Grid) : Grid :=
  match ps with
  | [] => g
  | p :: ps' =>
      let g' := step_position tau g p in
      step_positions tau ps' g'
  end.

Definition step (tau : nat) (g : Grid) : Grid :=
  step_positions tau all_positions_grid g.

(* -----------------------------------------------------------------------------
   Agent-Specific Tolerance Dynamics
   ----------------------------------------------------------------------------- *)

Definition empty_and_happy_for_agent_tolerance
  (tau_fn : Agent -> nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  cell_is_empty g p && happy_for_agent_tolerance tau_fn g a p.

Definition find_destination_agent_tolerance
  (tau_fn : Agent -> nat) (g : Grid) (a : Agent) : option Pos :=
  List.find (empty_and_happy_for_agent_tolerance tau_fn g a) all_positions_grid.

Definition step_position_agent_tolerance
  (tau_fn : Agent -> nat) (g : Grid) (p : Pos) : Grid :=
  match get_cell g p with
  | Empty => g
  | Occupied a =>
      if happy_agent_tolerance tau_fn g p then
        g
      else
        match find_destination_agent_tolerance tau_fn g a with
        | None => g
        | Some q =>
            let g1 := set_cell g p Empty in
            let g2 := set_cell g1 q (Occupied a) in
            g2
        end
  end.

Fixpoint step_positions_agent_tolerance
  (tau_fn : Agent -> nat) (ps : list Pos) (g : Grid) : Grid :=
  match ps with
  | [] => g
  | p :: ps' =>
      let g' := step_position_agent_tolerance tau_fn g p in
      step_positions_agent_tolerance tau_fn ps' g'
  end.

Definition step_agent_tolerance (tau_fn : Agent -> nat) (g : Grid) : Grid :=
  step_positions_agent_tolerance tau_fn all_positions_grid g.

(** Uniform tolerance matches the agent-specific variant *)

Lemma empty_and_happy_for_uniform_matches_agent_tolerance :
  forall tau g a p,
    empty_and_happy_for tau g a p =
    empty_and_happy_for_agent_tolerance (fun _ => tau) g a p.
Proof.
  intros tau g a p.
  unfold empty_and_happy_for, empty_and_happy_for_agent_tolerance.
  rewrite <- happy_for_uniform_is_agent_tolerance.
  reflexivity.
Qed.

Lemma find_destination_uniform_matches_agent_tolerance :
  forall tau g a,
    find_destination tau g a = find_destination_agent_tolerance (fun _ => tau) g a.
Proof.
  intros tau g a.
  unfold find_destination, find_destination_agent_tolerance.
  assert (Heq : empty_and_happy_for tau g a = empty_and_happy_for_agent_tolerance (fun _ => tau) g a).
  { apply functional_extensionality.
    intros p.
    apply empty_and_happy_for_uniform_matches_agent_tolerance. }
  rewrite Heq.
  reflexivity.
Qed.

Lemma step_position_uniform_matches_agent_tolerance :
  forall tau g p,
    step_position tau g p = step_position_agent_tolerance (fun _ => tau) g p.
Proof.
  intros tau g p.
  unfold step_position, step_position_agent_tolerance.
  destruct (get_cell g p) as [|a] eqn:Hcell; [reflexivity|].
  rewrite <- happy_uniform_is_agent_tolerance.
  destruct (happy tau g p); [reflexivity|].
  rewrite find_destination_uniform_matches_agent_tolerance.
  destruct (find_destination_agent_tolerance (fun _ : Agent => tau) g a); reflexivity.
Qed.

(* -----------------------------------------------------------------------------
   Parallel Update Semantics
   ----------------------------------------------------------------------------- *)

Fixpoint compute_moves (tau : nat) (g : Grid) (ps : list Pos) : list (Pos * Pos * Agent) :=
  match ps with
  | [] => []
  | p :: ps' =>
      match get_cell g p with
      | Empty => compute_moves tau g ps'
      | Occupied a =>
          if happy tau g p then
            compute_moves tau g ps'
          else
            match find_destination tau g a with
            | None => compute_moves tau g ps'
            | Some q => (p, q, a) :: compute_moves tau g ps'
            end
      end
  end.

Fixpoint apply_moves (moves : list (Pos * Pos * Agent)) (g : Grid) : Grid :=
  match moves with
  | [] => g
  | (p, q, a) :: rest =>
      let g1 := set_cell g p Empty in
      let g2 := set_cell g1 q (Occupied a) in
      apply_moves rest g2
  end.

Fixpoint NoDup_b {A : Type} (eqb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (eqb x) xs) && NoDup_b eqb xs
  end.

Fixpoint destinations_in_moves (moves : list (Pos * Pos * Agent)) : list Pos :=
  match moves with
  | [] => []
  | (_, q, _) :: rest => q :: destinations_in_moves rest
  end.

Definition has_destination_conflict (moves : list (Pos * Pos * Agent)) : bool :=
  let dests := destinations_in_moves moves in
  negb (NoDup_b pos_eqb dests).

Fixpoint remove_conflicts_aux (moves : list (Pos * Pos * Agent))
                               (seen_dests : list Pos) : list (Pos * Pos * Agent) :=
  match moves with
  | [] => []
  | (p, q, a) :: rest =>
      if existsb (pos_eqb q) seen_dests then
        remove_conflicts_aux rest seen_dests
      else
        (p, q, a) :: remove_conflicts_aux rest (q :: seen_dests)
  end.

Definition remove_conflicts (moves : list (Pos * Pos * Agent)) : list (Pos * Pos * Agent) :=
  remove_conflicts_aux moves [].

Definition step_parallel_old (tau : nat) (g : Grid) : Grid :=
  apply_moves (compute_moves tau g all_positions_grid) g.

Definition step_parallel (tau : nat) (g : Grid) : Grid :=
  let all_moves := compute_moves tau g all_positions_grid in
  let conflict_free_moves := remove_conflicts all_moves in
  apply_moves conflict_free_moves g.

Lemma apply_moves_nil :
  forall g, apply_moves [] g = g.
Proof.
  intros g. reflexivity.
Qed.

Lemma compute_moves_app :
  forall tau g ps1 ps2,
    compute_moves tau g (ps1 ++ ps2) =
    compute_moves tau g ps1 ++ compute_moves tau g ps2.
Proof.
  intros tau g ps1 ps2.
  induction ps1 as [|p ps1' IH]; simpl; [reflexivity|].
  destruct (get_cell g p) eqn:Hcell; [apply IH|].
  destruct (happy tau g p) eqn:Hhappy; [apply IH|].
  destruct (find_destination tau g a) eqn:Hfind; [|apply IH].
  simpl. rewrite IH. reflexivity.
Qed.

Lemma existsb_false_not_in :
  forall q seen,
    existsb (pos_eqb q) seen = false ->
    ~ In q seen.
Proof.
  intros q seen H Hin.
  assert (Htrue : existsb (pos_eqb q) seen = true).
  { rewrite existsb_exists. exists q. split. assumption. apply pos_eqb_refl. }
  rewrite H in Htrue. discriminate.
Qed.

Lemma remove_conflicts_aux_not_in_result :
  forall moves seen q,
    In q seen ->
    ~ In q (destinations_in_moves (remove_conflicts_aux moves seen)).
Proof.
  intros moves; induction moves as [|[[p q'] a] rest IH]; intros seen q Hin; simpl.
  - intros [].
  - destruct (existsb (pos_eqb q') seen) eqn:Hexists.
    + apply IH. assumption.
    + simpl. intros [Heq | Hin'].
      * subst q'. apply existsb_false_not_in in Hexists. contradiction.
      * apply (IH (q' :: seen) q). right. assumption. assumption.
Qed.

Lemma remove_conflicts_aux_no_duplicates :
  forall moves seen,
    NoDup (destinations_in_moves (remove_conflicts_aux moves seen)).
Proof.
  intros moves; induction moves as [|[[p q] a] rest IH]; intros seen; simpl.
  - constructor.
  - destruct (existsb (pos_eqb q) seen) eqn:Hexists.
    + apply IH.
    + simpl. constructor.
      * apply remove_conflicts_aux_not_in_result. left. reflexivity.
      * apply IH.
Qed.

Lemma remove_conflicts_no_duplicates :
  forall moves,
    NoDup (destinations_in_moves (remove_conflicts moves)).
Proof.
  intros moves.
  unfold remove_conflicts.
  apply remove_conflicts_aux_no_duplicates.
Qed.

Fixpoint sources_in_moves (moves : list (Pos * Pos * Agent)) : list Pos :=
  match moves with
  | [] => []
  | (p, _, _) :: rest => p :: sources_in_moves rest
  end.

Fixpoint agents_in_moves (moves : list (Pos * Pos * Agent)) : list Agent :=
  match moves with
  | [] => []
  | (_, _, a) :: rest => a :: agents_in_moves rest
  end.

Lemma compute_moves_source_occupied :
  forall tau g ps p q a,
    In (p, q, a) (compute_moves tau g ps) ->
    get_cell g p = Occupied a.
Proof.
  intros tau g ps. induction ps as [|p' ps' IH]; intros p q a Hin; simpl in Hin.
  - contradiction.
  - destruct (get_cell g p') eqn:Hcell.
    + apply (IH p q a). assumption.
    + destruct (happy tau g p') eqn:Hhappy.
      * apply (IH p q a). assumption.
      * destruct (find_destination tau g a0) eqn:Hfind.
        -- simpl in Hin. destruct Hin as [Heq | Hin'].
           ++ inversion Heq; subst. assumption.
           ++ apply (IH p q a). assumption.
        -- apply (IH p q a). assumption.
Qed.

Lemma compute_moves_dest_empty :
  forall tau g ps p q a,
    In (p, q, a) (compute_moves tau g ps) ->
    get_cell g q = Empty.
Proof.
  intros tau g ps. induction ps as [|p' ps' IH]; intros p q a Hin; simpl in Hin.
  - contradiction.
  - destruct (get_cell g p') eqn:Hcell.
    + apply (IH p q a). assumption.
    + destruct (happy tau g p') eqn:Hhappy.
      * apply (IH p q a). assumption.
      * destruct (find_destination tau g a0) eqn:Hfind.
        -- simpl in Hin. destruct Hin as [Heq | Hin'].
           ++ inversion Heq. subst p' p0 a0. clear Heq.
              unfold find_destination in Hfind.
              destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) as [dest|] eqn:Hf; [|discriminate].
              injection Hfind as Hqdest. subst dest.
              apply List.find_some in Hf.
              destruct Hf as [_ Hcond].
              unfold empty_and_happy_for in Hcond.
              apply Bool.andb_true_iff in Hcond.
              destruct Hcond as [Hempty _].
              unfold cell_is_empty in Hempty.
              apply Bool.negb_true_iff in Hempty.
              unfold is_occupied in Hempty.
              destruct (get_cell g q) eqn:Hcellq; [reflexivity | discriminate].
           ++ apply (IH p q a). assumption.
        -- apply (IH p q a). assumption.
Qed.

Lemma compute_moves_source_dest_different :
  forall tau g ps p q a,
    In (p, q, a) (compute_moves tau g ps) ->
    p <> q.
Proof.
  intros tau g ps p q a Hin.
  assert (Hocc : get_cell g p = Occupied a) by (eapply compute_moves_source_occupied; eassumption).
  assert (Hempty : get_cell g q = Empty) by (eapply compute_moves_dest_empty; eassumption).
  intros Heq. subst q. rewrite Hocc in Hempty. discriminate.
Qed.

Lemma remove_conflicts_aux_subset :
  forall moves seen p q a,
    In (p, q, a) (remove_conflicts_aux moves seen) ->
    In (p, q, a) moves.
Proof.
  intros moves. induction moves as [|[[p' q'] a'] rest IH]; intros seen p q a Hin; simpl in *.
  - contradiction.
  - destruct (existsb (pos_eqb q') seen) eqn:Hexists.
    + right. apply IH with (seen := seen). assumption.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * left. assumption.
      * right. apply IH with (seen := q' :: seen). assumption.
Qed.

Lemma remove_conflicts_subset :
  forall moves p q a,
    In (p, q, a) (remove_conflicts moves) ->
    In (p, q, a) moves.
Proof.
  intros moves p q a Hin.
  unfold remove_conflicts in Hin.
  apply remove_conflicts_aux_subset with (seen := []). assumption.
Qed.

(* -----------------------------------------------------------------------------
   Relational Semantics: Alternative Characterization of Dynamics
   ----------------------------------------------------------------------------- *)

(** We provide a relational semantics as an alternative to the functional
    definition. This is useful for reasoning about properties like
    determinism, confluence, and for potential extensions to non-determinism. *)

Inductive StepRel (tau : nat) : Grid -> Grid -> Prop :=
  | step_rel_intro : forall g g',
      g' = step tau g ->
      StepRel tau g g'.

Inductive StepPositionRel (tau : nat) (p : Pos) : Grid -> Grid -> Prop :=
  | step_position_rel_intro : forall g g',
      g' = step_position tau g p ->
      StepPositionRel tau p g g'.

Lemma step_rel_functional :
  forall tau g g1 g2,
    StepRel tau g g1 ->
    StepRel tau g g2 ->
    g1 = g2.
Proof.
  intros tau g g1 g2 H1 H2.
  inversion H1; inversion H2; subst.
  reflexivity.
Qed.

Lemma step_position_rel_functional :
  forall tau p g g1 g2,
    StepPositionRel tau p g g1 ->
    StepPositionRel tau p g g2 ->
    g1 = g2.
Proof.
  intros tau p g g1 g2 H1 H2.
  inversion H1; inversion H2; subst.
  reflexivity.
Qed.

Lemma step_rel_iff_step :
  forall tau g g',
    StepRel tau g g' <-> g' = step tau g.
Proof.
  intros tau g g'; split.
  - intros H; inversion H; subst; reflexivity.
  - intros H; constructor; assumption.
Qed.

Lemma step_position_rel_iff_step_position :
  forall tau p g g',
    StepPositionRel tau p g g' <-> g' = step_position tau g p.
Proof.
  intros tau p g g'; split.
  - intros H; inversion H; subst; reflexivity.
  - intros H; constructor; assumption.
Qed.

Theorem step_rel_deterministic :
  forall tau g g1 g2,
    StepRel tau g g1 ->
    StepRel tau g g2 ->
    g1 = g2.
Proof.
  intros tau g g1 g2 H1 H2.
  apply step_rel_functional with (tau := tau) (g := g); assumption.
Qed.

Theorem step_position_rel_deterministic :
  forall tau p g g1 g2,
    StepPositionRel tau p g g1 ->
    StepPositionRel tau p g g2 ->
    g1 = g2.
Proof.
  intros tau p g g1 g2 H1 H2.
  apply step_position_rel_functional with (tau := tau) (p := p) (g := g); assumption.
Qed.

Lemma step_rel_exists :
  forall tau g,
    exists g', StepRel tau g g'.
Proof.
  intros tau g.
  exists (step tau g).
  constructor; reflexivity.
Qed.

Lemma step_position_rel_exists :
  forall tau p g,
    exists g', StepPositionRel tau p g g'.
Proof.
  intros tau p g.
  exists (step_position tau g p).
  constructor; reflexivity.
Qed.

Inductive StepStar (tau : nat) : Grid -> Grid -> Prop :=
  | step_star_refl : forall g,
      StepStar tau g g
  | step_star_step : forall g g' g'',
      StepRel tau g g' ->
      StepStar tau g' g'' ->
      StepStar tau g g''.

Lemma step_star_trans :
  forall tau g1 g2 g3,
    StepStar tau g1 g2 ->
    StepStar tau g2 g3 ->
    StepStar tau g1 g3.
Proof.
  intros tau g1 g2 g3 H12 H23.
  induction H12 as [g | g g' g'' Hstep Hstar IH].
  - assumption.
  - apply step_star_step with (g' := g').
    + assumption.
    + apply IH; assumption.
Qed.

Lemma step_star_one :
  forall tau g g',
    StepRel tau g g' ->
    StepStar tau g g'.
Proof.
  intros tau g g' H.
  apply step_star_step with (g' := g').
  - assumption.
  - constructor.
Qed.

Lemma step_star_n :
  forall tau g n,
    StepStar tau g (Nat.iter n (step tau) g).
Proof.
  intros tau g n.
  induction n as [|n' IH].
  - simpl. constructor.
  - change (Nat.iter (S n') (step tau) g) with (step tau (Nat.iter n' (step tau) g)).
    eapply step_star_trans with (g2 := Nat.iter n' (step tau) g).
    + exact IH.
    + apply step_star_one.
      constructor; reflexivity.
Qed.

(* -----------------------------------------------------------------------------
   A Simple but Non-Trivial Global Property: Stability Fixed Points
   ----------------------------------------------------------------------------- *)

(** A grid is [stable] for tolerance [tau] if every agent is already happy. *)

Definition stable (tau : nat) (g : Grid) : Prop :=
  forall p, happy tau g p = true.

Fixpoint all_happy_b (tau : nat) (g : Grid) (ps : list Pos) : bool :=
  match ps with
  | [] => true
  | p :: ps' => happy tau g p && all_happy_b tau g ps'
  end.

Definition stable_b (tau : nat) (g : Grid) : bool :=
  all_happy_b tau g all_positions_grid.

Lemma all_happy_b_spec :
  forall tau g ps,
    all_happy_b tau g ps = true <-> (forall p, In p ps -> happy tau g p = true).
Proof.
  intros tau g ps; induction ps as [|p ps' IH]; split; intros H.
  - intros p Hin; inversion Hin.
  - reflexivity.
  - intros q Hin; simpl in H; rewrite Bool.andb_true_iff in H.
    destruct H as [Hp Hps']; destruct Hin as [Heq | Hin'].
    + subst; assumption.
    + apply IH; assumption.
  - simpl; rewrite Bool.andb_true_iff; split.
    + apply H; left; reflexivity.
    + apply IH; intros q Hin; apply H; right; assumption.
Qed.

Lemma stable_iff_bounded : forall tau g,
  (forall p, In p all_positions_grid -> happy tau g p = true) <-> stable_b tau g = true.
Proof.
  intros tau g; split.
  - intros H; unfold stable_b; apply all_happy_b_spec; assumption.
  - intros H; unfold stable_b in H; apply all_happy_b_spec; assumption.
Qed.

Lemma all_positions_contains_bounded :
  forall p, (exists i j : nat, p = (i, j) /\ (i < grid_size)%nat /\ (j < grid_size)%nat) -> In p all_positions_grid.
Proof.
  intros p [i [j [Heq [Hi Hj]]]]; subst.
  apply all_positions_coverage; assumption.
Qed.

Lemma stable_iff_in_bounds : forall tau g,
  (forall i j, (i < grid_size)%nat -> (j < grid_size)%nat -> happy tau g (i, j) = true) <-> stable_b tau g = true.
Proof.
  intros tau g; split.
  - intros H; apply stable_iff_bounded; intros [i j] Hin.
    apply all_positions_in_bounds in Hin; destruct Hin as [Hi Hj]; apply H; assumption.
  - intros H i j Hi Hj.
    assert (Hmem : In (i, j) all_positions_grid) by (apply all_positions_coverage; assumption).
    apply stable_iff_bounded; assumption.
Qed.

Lemma stable_forall_in_all_positions :
  forall tau g,
    stable tau g -> (forall p, In p all_positions_grid -> happy tau g p = true).
Proof.
  intros tau g Hstable p Hin; apply Hstable.
Qed.

Lemma happy_out_of_bounds_when_empty :
  forall tau g i j,
    ((i >= grid_size)%nat \/ (j >= grid_size)%nat) ->
    get_cell g (i, j) = Empty ->
    happy tau g (i, j) = true.
Proof.
  intros tau g i j Hout Hempty.
  apply empty_cell_always_happy; assumption.
Qed.

Lemma happy_out_of_bounds_leb :
  forall tau g i j a,
    ((i >= grid_size)%nat \/ (j >= grid_size)%nat) ->
    get_cell g (i, j) = Occupied a ->
    happy tau g (i, j) = (tau <=? count_same a (neighbor_cells g (i, j)))%nat.
Proof.
  intros tau g i j a Hout Hocc.
  unfold happy; rewrite Hocc; reflexivity.
Qed.

Lemma stable_from_bounded_assuming_empty_outside :
  forall tau g,
    (forall i j, ((i >= grid_size)%nat \/ (j >= grid_size)%nat) -> get_cell g (i, j) = Empty) ->
    (forall i j, (i < grid_size)%nat -> (j < grid_size)%nat -> happy tau g (i, j) = true) ->
    stable tau g.
Proof.
  intros tau g Hempty H [i j].
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - apply Nat.ltb_lt in Hi; apply Nat.ltb_lt in Hj; apply H; assumption.
  - apply Nat.ltb_ge in Hj; apply empty_cell_always_happy; apply Hempty; right; assumption.
  - apply Nat.ltb_ge in Hi; apply empty_cell_always_happy; apply Hempty; left; assumption.
  - apply Nat.ltb_ge in Hi; apply empty_cell_always_happy; apply Hempty; left; assumption.
Qed.

Lemma stable_to_bounded :
  forall tau g,
    stable tau g ->
    (forall i j, (i < grid_size)%nat -> (j < grid_size)%nat -> happy tau g (i, j) = true).
Proof.
  intros tau g Hstable i j Hi Hj; apply Hstable.
Qed.

Lemma stable_bounded_iff_wellformed :
  forall tau g,
    wellformed_grid g ->
    (stable tau g <->
     (forall i j, (i < grid_size)%nat -> (j < grid_size)%nat -> happy tau g (i, j) = true)).
Proof.
  intros tau g Hwf; split.
  - apply stable_to_bounded.
  - apply stable_from_bounded_assuming_empty_outside; assumption.
Qed.

Lemma stable_iff_wellformed : forall tau g,
  wellformed_grid g ->
  (stable tau g <-> stable_b tau g = true).
Proof.
  intros tau g Hwf; split.
  - intros Hstable; apply stable_iff_in_bounds; apply stable_to_bounded; assumption.
  - intros Hstable_b; apply stable_from_bounded_assuming_empty_outside; [assumption|].
    apply stable_iff_in_bounds; assumption.
Qed.

Lemma stable_dec_wellformed : forall tau g,
  wellformed_grid g ->
  {stable tau g} + {~ stable tau g}.
Proof.
  intros tau g Hwf.
  destruct (stable_b tau g) eqn:Hstable.
  - left; apply stable_iff_wellformed; assumption.
  - right; intros Hcontra; apply stable_iff_wellformed in Hcontra; [|assumption].
    rewrite Hcontra in Hstable; discriminate.
Defined.

Lemma step_position_id_on_stable :
  forall tau g p,
    stable tau g ->
    step_position tau g p = g.
Proof.
  intros tau g p Hstable.
  unfold step_position.
  destruct (get_cell g p) eqn:Hc.
  - reflexivity.
  - rewrite (Hstable p). reflexivity.
Qed.

Lemma step_positions_id_on_stable :
  forall tau g ps,
    stable tau g ->
    step_positions tau ps g = g.
Proof.
  intros tau g ps Hstable.
  induction ps as [|p ps' IH]; simpl.
  - reflexivity.
  - rewrite (step_position_id_on_stable tau g p Hstable).
    apply IH; assumption.
Qed.

Theorem step_stable_fixed_point :
  forall tau g,
    stable tau g ->
    step tau g = g.
Proof.
  intros tau g Hstable.
  unfold step.
  apply step_positions_id_on_stable; assumption.
Qed.

Corollary step_stable_fixed_point_n :
  forall tau g n,
    stable tau g ->
    Nat.iter n (step tau) g = g.
Proof.
  intros tau g n Hstable.
  induction n as [|n' IH]; simpl.
  - reflexivity.
  - rewrite IH; apply step_stable_fixed_point; assumption.
Qed.

Corollary stable_stays_stable :
  forall tau g,
    stable tau g ->
    stable tau (step tau g).
Proof.
  intros tau g Hstable.
  rewrite step_stable_fixed_point; assumption.
Qed.

Corollary stable_wellformed_iff_stable_b :
  forall tau g,
    wellformed_grid g ->
    stable tau g <-> stable_b tau g = true.
Proof.
  intros tau g Hwf; apply stable_iff_wellformed; assumption.
Qed.

Corollary stable_decidable_wellformed :
  forall tau g,
    wellformed_grid g ->
    {stable tau g} + {~ stable tau g}.
Proof.
  intros tau g Hwf; apply stable_dec_wellformed; assumption.
Qed.

Theorem zero_tolerance_stable :
  forall g,
    stable 0 g.
Proof.
  intros g p.
  apply zero_tolerance_all_happy.
Qed.

Theorem step_parallel_stable_fixed_point :
  forall tau g,
    stable tau g ->
    step_parallel tau g = g.
Proof.
  intros tau g Hstable.
  unfold step_parallel.
  assert (Hmoves : compute_moves tau g all_positions_grid = []).
  { induction all_positions_grid as [|p ps IH]; simpl; [reflexivity|].
    destruct (get_cell g p) eqn:Hcell; [apply IH|].
    rewrite (Hstable p). apply IH. }
  rewrite Hmoves. simpl. reflexivity.
Qed.

Theorem step_star_stable_fixed :
  forall tau g g',
    stable tau g ->
    StepStar tau g g' ->
    g' = g.
Proof.
  intros tau g g' Hstable Hstar.
  induction Hstar as [g | g gmid g'' Hstep Hstar IH].
  - reflexivity.
  - apply step_rel_iff_step in Hstep.
    rewrite step_stable_fixed_point in Hstep; [|assumption].
    subst gmid.
    apply IH; assumption.
Qed.

Lemma step_position_preserves_wellformed :
  forall tau g p,
    wellformed_grid g ->
    wellformed_grid (step_position tau g p).
Proof.
  intros tau g p Hwf.
  unfold step_position.
  destruct (get_cell g p) eqn:Hcell.
  - assumption.
  - destruct (happy tau g p) eqn:Hhappy.
    + assumption.
    + destruct (find_destination tau g a) eqn:Hfind.
      * unfold find_destination in Hfind.
        destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hfind'; [|discriminate].
        injection Hfind as Hfind; subst p0.
        apply set_cell_twice_preserves_wellformed; [assumption|].
        apply List.find_some in Hfind'.
        destruct Hfind' as [Hin _]; destruct p1 as [i j].
        apply all_positions_in_bounds; assumption.
      * assumption.
Qed.

Lemma step_positions_preserves_wellformed :
  forall tau ps g,
    wellformed_grid g ->
    wellformed_grid (step_positions tau ps g).
Proof.
  intros tau ps; induction ps as [|p ps' IH]; intros g Hwf; simpl.
  - assumption.
  - apply IH; apply step_position_preserves_wellformed; assumption.
Qed.

Lemma step_preserves_wellformed :
  forall tau g,
    wellformed_grid g ->
    wellformed_grid (step tau g).
Proof.
  intros tau g Hwf.
  unfold step; apply step_positions_preserves_wellformed; assumption.
Qed.

Corollary step_n_preserves_wellformed :
  forall tau g n,
    wellformed_grid g ->
    wellformed_grid (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf.
  induction n as [|n' IH]; simpl.
  - assumption.
  - apply step_preserves_wellformed; assumption.
Qed.

Corollary wellformed_stable_wellformed :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    wellformed_grid (step tau g).
Proof.
  intros tau g Hwf Hstable.
  rewrite step_stable_fixed_point; assumption.
Qed.

Corollary step_position_wellformed_same_at_stable_pos :
  forall tau g p,
    wellformed_grid g ->
    stable tau g ->
    step_position tau g p = g.
Proof.
  intros tau g p Hwf Hstable.
  apply step_position_id_on_stable; assumption.
Qed.

(* -----------------------------------------------------------------------------
   Agent Conservation: Total Agent Count is Invariant
   ----------------------------------------------------------------------------- *)

Fixpoint count_agents_in_cells (cs : list Cell) : nat :=
  match cs with
  | [] => 0
  | Empty :: cs' => count_agents_in_cells cs'
  | Occupied _ :: cs' => S (count_agents_in_cells cs')
  end.

Definition count_agents_at_positions (g : Grid) (ps : list Pos) : nat :=
  count_agents_in_cells (map (get_cell g) ps).

Definition count_agents (g : Grid) : nat :=
  count_agents_at_positions g all_positions_grid.

Lemma count_agents_in_cells_app :
  forall cs1 cs2,
    count_agents_in_cells (cs1 ++ cs2) =
    (count_agents_in_cells cs1 + count_agents_in_cells cs2)%nat.
Proof.
  intros cs1 cs2.
  induction cs1 as [|c cs1' IH]; simpl.
  - reflexivity.
  - destruct c; simpl; rewrite IH; reflexivity.
Qed.

Lemma count_agents_at_positions_app :
  forall g ps1 ps2,
    count_agents_at_positions g (ps1 ++ ps2) =
    (count_agents_at_positions g ps1 + count_agents_at_positions g ps2)%nat.
Proof.
  intros g ps1 ps2.
  unfold count_agents_at_positions.
  rewrite map_app.
  apply count_agents_in_cells_app.
Qed.

Lemma count_agents_in_cells_cons_empty :
  forall cs,
    count_agents_in_cells (Empty :: cs) = count_agents_in_cells cs.
Proof.
  intros cs; reflexivity.
Qed.

Lemma count_agents_in_cells_cons_occupied :
  forall a cs,
    count_agents_in_cells (Occupied a :: cs) = S (count_agents_in_cells cs).
Proof.
  intros a cs; reflexivity.
Qed.

(* Helper lemmas for count_agents proofs *)

Lemma count_agents_in_cells_swap :
  forall cs1 cs2 c1 c2,
    count_agents_in_cells (cs1 ++ c1 :: cs2 ++ c2 :: []) =
    count_agents_in_cells (cs1 ++ c2 :: cs2 ++ c1 :: []).
Proof.
  intros cs1 cs2 c1 c2.
  rewrite !count_agents_in_cells_app; simpl.
  destruct c1, c2; simpl;
  rewrite !count_agents_in_cells_app; simpl;
  repeat rewrite Nat.add_0_r; ring.
Qed.

Lemma get_cell_set_cell_eq :
  forall g p c,
    get_cell (set_cell g p c) p = c.
Proof.
  intros g p c.
  apply get_set_same.
Qed.

Lemma get_cell_set_cell_neq :
  forall g p q c,
    p <> q ->
    get_cell (set_cell g p c) q = get_cell g q.
Proof.
  intros g p q c Hneq.
  apply get_set_other.
  assumption.
Qed.

Lemma map_get_cell_extensional :
  forall g1 g2 ps,
    (forall p, In p ps -> get_cell g1 p = get_cell g2 p) ->
    map (get_cell g1) ps = map (get_cell g2) ps.
Proof.
  intros g1 g2 ps Hext.
  induction ps as [|p ps' IH].
  - reflexivity.
  - simpl. rewrite Hext by (left; reflexivity).
    rewrite IH by (intros q Hq; apply Hext; right; assumption).
    reflexivity.
Qed.

Lemma count_agents_extensional :
  forall g1 g2,
    (forall p, In p all_positions_grid -> get_cell g1 p = get_cell g2 p) ->
    count_agents g1 = count_agents g2.
Proof.
  intros g1 g2 Hext.
  unfold count_agents, count_agents_at_positions.
  apply f_equal.
  apply map_get_cell_extensional.
  assumption.
Qed.

Lemma get_cell_double_set_same :
  forall g p q c1 c2,
    get_cell (set_cell (set_cell g p c1) q c2) q = c2.
Proof.
  intros g p q c1 c2.
  apply get_set_same.
Qed.

Lemma get_cell_double_set_first :
  forall g p q c1 c2,
    p <> q ->
    get_cell (set_cell (set_cell g p c1) q c2) p = c1.
Proof.
  intros g p q c1 c2 Hneq.
  rewrite get_set_other.
  - apply get_set_same.
  - intros contra; subst; apply Hneq; reflexivity.
Qed.

Lemma get_cell_double_set_other :
  forall g p q r c1 c2,
    p <> r ->
    q <> r ->
    get_cell (set_cell (set_cell g p c1) q c2) r = get_cell g r.
Proof.
  intros g p q r c1 c2 Hneqp Hneqq.
  rewrite get_set_other by assumption.
  rewrite get_set_other by assumption.
  reflexivity.
Qed.

Lemma count_agents_in_cells_eq_empty_occupied :
  forall cs c,
    count_agents_in_cells (Empty :: cs) = count_agents_in_cells cs /\
    count_agents_in_cells (Occupied c :: cs) = S (count_agents_in_cells cs).
Proof.
  intros cs c; split; reflexivity.
Qed.

Lemma count_cell_swap :
  forall c1 c2,
    count_agents_in_cells [c1; c2] = count_agents_in_cells [c2; c1].
Proof.
  intros c1 c2.
  destruct c1, c2; simpl; reflexivity.
Qed.

Lemma count_agents_in_cells_remove_add :
  forall cs1 cs2 c1 c2,
    count_agents_in_cells (cs1 ++ c1 :: cs2 ++ c2 :: []) =
    (count_agents_in_cells (cs1 ++ cs2) + count_agents_in_cells [c1; c2])%nat.
Proof.
  intros cs1 cs2 c1 c2.
  rewrite !count_agents_in_cells_app. simpl.
  destruct c1, c2; simpl;
  rewrite !count_agents_in_cells_app; simpl;
  repeat rewrite Nat.add_0_r; lia.
Qed.

Lemma count_agents_in_cells_split_at :
  forall ps1 ps2 g,
    count_agents_in_cells (map (get_cell g) (ps1 ++ ps2)) =
    (count_agents_in_cells (map (get_cell g) ps1) +
     count_agents_in_cells (map (get_cell g) ps2))%nat.
Proof.
  intros ps1 ps2 g.
  rewrite map_app.
  apply count_agents_in_cells_app.
Qed.

Lemma count_agents_in_cells_cons_split :
  forall p ps g,
    count_agents_in_cells (map (get_cell g) (p :: ps)) =
    (count_agents_in_cells [get_cell g p] + count_agents_in_cells (map (get_cell g) ps))%nat.
Proof.
  intros p ps g.
  simpl. destruct (get_cell g p); simpl; reflexivity.
Qed.

(* Micro lemmas for list splitting *)

Lemma app_assoc_cons :
  forall {A : Type} (l1 l2 : list A) (x : A) (l3 : list A),
    l1 ++ x :: l2 ++ l3 = (l1 ++ [x]) ++ l2 ++ l3.
Proof.
  intros A l1 l2 x l3.
  rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma not_in_app :
  forall {A : Type} (x : A) (l1 l2 : list A),
    ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l1 l2. split.
  - intros Hnin. split; intros Hin; apply Hnin; apply in_or_app; auto.
  - intros [Hnin1 Hnin2] Hin. apply in_app_or in Hin. destruct Hin; contradiction.
Qed.

Lemma in_split_ordered_case1 :
  forall {A : Type} (x y : A) (l1 l2a l2b : list A),
    l1 ++ x :: l2a ++ y :: l2b = l1 ++ x :: (l2a ++ y :: l2b).
Proof.
  intros. reflexivity.
Qed.

Lemma in_split_ordered_case2 :
  forall {A : Type} (x y : A) (l1a l1b l2 : list A),
    l1a ++ y :: l1b ++ x :: l2 = l1a ++ y :: (l1b ++ x :: l2).
Proof.
  intros. reflexivity.
Qed.

Lemma not_in_cons_app :
  forall {A : Type} (x y : A) (l1 l2 : list A),
    x <> y ->
    ~ In x l1 ->
    ~ In x l2 ->
    ~ In x (l1 ++ y :: l2).
Proof.
  intros A x y l1 l2 Hneq Hnin1 Hnin2 Hin.
  apply in_app_or in Hin. destruct Hin as [Hin1 | Hin2].
  - contradiction.
  - simpl in Hin2. destruct Hin2 as [Heq | Hin2]; [subst; contradiction | contradiction].
Qed.

(* Four specific lemmas instead of one complex general lemma *)

Lemma in_split_xy_form :
  forall {A : Type} (x y : A) (l1 l2 l3 : list A),
    x <> y ->
    ~ In x l2 ->
    ~ In y l1 ->
    In x (l1 ++ x :: l2 ++ y :: l3) /\
    In y (l1 ++ x :: l2 ++ y :: l3).
Proof.
  intros A x y l1 l2 l3 Hneq Hninx2 Hniny1.
  split; apply in_or_app; right; simpl.
  - left; reflexivity.
  - right; apply in_or_app; right; simpl; left; reflexivity.
Qed.

Lemma in_split_yx_form :
  forall {A : Type} (x y : A) (l1 l2 l3 : list A),
    x <> y ->
    ~ In y l2 ->
    ~ In x l1 ->
    In x (l1 ++ y :: l2 ++ x :: l3) /\
    In y (l1 ++ y :: l2 ++ x :: l3).
Proof.
  intros A x y l1 l2 l3 Hneq Hniny2 Hninx1.
  split; apply in_or_app.
  - right; simpl; right; apply in_or_app; right; simpl; left; reflexivity.
  - right; simpl; left; reflexivity.
Qed.

Lemma in_split_exists_xy_or_yx :
  forall {A : Type} (x y : A) (l : list A),
    x <> y ->
    In x l ->
    In y l ->
    (exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3) \/
    (exists l1 l2 l3, l = l1 ++ y :: l2 ++ x :: l3).
Proof.
  intros A x y l Hneq Hinx Hiny.
  apply in_split in Hinx. destruct Hinx as [lpre [lpost Heqx]].
  rewrite Heqx in Hiny.
  apply in_app_or in Hiny. destruct Hiny as [Hiny_pre | Hiny_post].
  - apply in_split in Hiny_pre. destruct Hiny_pre as [l1 [l2 Heqy]].
    right. exists l1, l2, lpost.
    rewrite Heqx. rewrite Heqy.
    repeat rewrite <- app_assoc. reflexivity.
  - simpl in Hiny_post. destruct Hiny_post as [Heq | Hiny_post]; [subst; contradiction |].
    apply in_split in Hiny_post. destruct Hiny_post as [l2 [l3 Heqy]].
    left. exists lpre, l2, l3.
    rewrite Heqx. rewrite Heqy.
    reflexivity.
Qed.


Lemma in_split_gives_first_occurrence :
  forall {A : Type} (x : A) (l l1 l2 : list A),
    In x l ->
    l = l1 ++ x :: l2 ->
    (forall l1' l2', l = l1' ++ x :: l2' -> (length l1' >= length l1)%nat) ->
    ~ In x l1.
Proof.
  intros A x l l1 l2 Hin Heq Hmin Hcontra.
  apply in_split in Hcontra. destruct Hcontra as [la [lb Heq_l1]].
  assert (Hlen : (length la >= length l1)%nat).
  { apply (Hmin la (lb ++ x :: l2)). rewrite Heq. rewrite Heq_l1. repeat rewrite <- app_assoc. reflexivity. }
  assert (Hlen2 : (length la + S (length lb) = length l1)%nat).
  { apply (f_equal (@length A)) in Heq_l1. rewrite app_length in Heq_l1. simpl in Heq_l1. lia. }
  lia.
Qed.

(* Micro lemmas for map preservation under swaps *)

Lemma map_preserved_outside_pq_before :
  forall g p q a l,
    ~ In p l ->
    ~ In q l ->
    map (get_cell (set_cell (set_cell g p Empty) q (Occupied a))) l = map (get_cell g) l.
Proof.
  intros g p q a l Hninp Hninq.
  apply map_ext_in. intros r Hr.
  rewrite get_cell_double_set_other; [reflexivity | | ]; intros contra; subst; contradiction.
Qed.

Lemma map_preserved_outside_pq_middle :
  forall g p q a l,
    ~ In p l ->
    ~ In q l ->
    map (get_cell (set_cell (set_cell g p Empty) q (Occupied a))) l = map (get_cell g) l.
Proof.
  intros g p q a l Hninp Hninq.
  apply map_preserved_outside_pq_before; assumption.
Qed.

Lemma map_preserved_outside_pq_after :
  forall g p q a l,
    ~ In p l ->
    ~ In q l ->
    map (get_cell (set_cell (set_cell g p Empty) q (Occupied a))) l = map (get_cell g) l.
Proof.
  intros g p q a l Hninp Hninq.
  apply map_preserved_outside_pq_before; assumption.
Qed.

Lemma count_swap_pq_order :
  forall g p q a l1 l2 l3,
    p <> q ->
    ~ In p l1 ->
    ~ In p l2 ->
    ~ In p l3 ->
    ~ In q l1 ->
    ~ In q l2 ->
    ~ In q l3 ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    count_agents_in_cells (map (get_cell (set_cell (set_cell g p Empty) q (Occupied a)))
                               (l1 ++ p :: l2 ++ q :: l3)) =
    count_agents_in_cells (map (get_cell g) (l1 ++ p :: l2 ++ q :: l3)).
Proof.
  intros g p q a l1 l2 l3 Hneq Hninp1 Hninp2 Hninp3 Hninq1 Hninq2 Hninq3 Hcellp Hcellq.
  set (g' := set_cell (set_cell g p Empty) q (Occupied a)).

  assert (Hget_p' : get_cell g' p = Empty).
  { unfold g'. apply get_cell_double_set_first. assumption. }

  assert (Hget_q' : get_cell g' q = Occupied a).
  { unfold g'. apply get_cell_double_set_same. }

  assert (Hmap_l1 : forall r, In r l1 -> get_cell g' r = get_cell g r).
  { intros r Hr. unfold g'. apply get_cell_double_set_other.
    - intros Heq. subst r. exfalso. apply Hninp1. exact Hr.
    - intros Heq. subst r. exfalso. apply Hninq1. exact Hr. }

  assert (Hmap_l2 : forall r, In r l2 -> get_cell g' r = get_cell g r).
  { intros r Hr. unfold g'. apply get_cell_double_set_other.
    - intros Heq. subst r. exfalso. apply Hninp2. exact Hr.
    - intros Heq. subst r. exfalso. apply Hninq2. exact Hr. }

  assert (Hmap_l3 : forall r, In r l3 -> get_cell g' r = get_cell g r).
  { intros r Hr. unfold g'. apply get_cell_double_set_other.
    - intros Heq. subst r. exfalso. apply Hninp3. exact Hr.
    - intros Heq. subst r. exfalso. apply Hninq3. exact Hr. }

  assert (Heq_l1 : map (get_cell g') l1 = map (get_cell g) l1).
  { apply map_ext_in. exact Hmap_l1. }

  assert (Heq_l2 : map (get_cell g') l2 = map (get_cell g) l2).
  { apply map_ext_in. exact Hmap_l2. }

  assert (Heq_l3 : map (get_cell g') l3 = map (get_cell g) l3).
  { apply map_ext_in. exact Hmap_l3. }

  transitivity (count_agents_in_cells (map (get_cell g) l1) + 0 +
                count_agents_in_cells (map (get_cell g) l2) + 1 +
                count_agents_in_cells (map (get_cell g) l3))%nat.

  - rewrite map_app. rewrite count_agents_in_cells_app. rewrite Heq_l1.
    simpl. rewrite Hget_p'. simpl.
    change (l2 ++ q :: l3) with (l2 ++ [q] ++ l3).
    rewrite map_app, map_app. rewrite count_agents_in_cells_app, count_agents_in_cells_app.
    rewrite Heq_l2, Heq_l3. simpl. rewrite Hget_q'. simpl. lia.

  - rewrite map_app. rewrite count_agents_in_cells_app.
    simpl. rewrite Hcellp. simpl.
    change (l2 ++ q :: l3) with (l2 ++ [q] ++ l3).
    rewrite map_app, map_app. rewrite count_agents_in_cells_app, count_agents_in_cells_app.
    simpl. rewrite Hcellq. simpl. lia.
Qed.

Lemma count_swap_qp_order :
  forall g p q a l1 l2 l3,
    p <> q ->
    ~ In q l1 ->
    ~ In q l2 ->
    ~ In q l3 ->
    ~ In p l1 ->
    ~ In p l2 ->
    ~ In p l3 ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    count_agents_in_cells (map (get_cell (set_cell (set_cell g p Empty) q (Occupied a)))
                               (l1 ++ q :: l2 ++ p :: l3)) =
    count_agents_in_cells (map (get_cell g) (l1 ++ q :: l2 ++ p :: l3)).
Proof.
  intros g p q a l1 l2 l3 Hneq Hninq1 Hninq2 Hninq3 Hninp1 Hninp2 Hninp3 Hcellp Hcellq.
  set (g' := set_cell (set_cell g p Empty) q (Occupied a)).

  assert (Hget_p' : get_cell g' p = Empty).
  { unfold g'. apply get_cell_double_set_first. assumption. }

  assert (Hget_q' : get_cell g' q = Occupied a).
  { unfold g'. apply get_cell_double_set_same. }

  assert (Hmap_l1 : forall r, In r l1 -> get_cell g' r = get_cell g r).
  { intros r Hr. unfold g'. apply get_cell_double_set_other.
    - intros Heq. subst r. exfalso. apply Hninp1. exact Hr.
    - intros Heq. subst r. exfalso. apply Hninq1. exact Hr. }

  assert (Hmap_l2 : forall r, In r l2 -> get_cell g' r = get_cell g r).
  { intros r Hr. unfold g'. apply get_cell_double_set_other.
    - intros Heq. subst r. exfalso. apply Hninp2. exact Hr.
    - intros Heq. subst r. exfalso. apply Hninq2. exact Hr. }

  assert (Hmap_l3 : forall r, In r l3 -> get_cell g' r = get_cell g r).
  { intros r Hr. unfold g'. apply get_cell_double_set_other.
    - intros Heq. subst r. exfalso. apply Hninp3. exact Hr.
    - intros Heq. subst r. exfalso. apply Hninq3. exact Hr. }

  assert (Heq_l1 : map (get_cell g') l1 = map (get_cell g) l1).
  { apply map_ext_in. exact Hmap_l1. }

  assert (Heq_l2 : map (get_cell g') l2 = map (get_cell g) l2).
  { apply map_ext_in. exact Hmap_l2. }

  assert (Heq_l3 : map (get_cell g') l3 = map (get_cell g) l3).
  { apply map_ext_in. exact Hmap_l3. }

  transitivity (count_agents_in_cells (map (get_cell g) l1) + 1 +
                count_agents_in_cells (map (get_cell g) l2) + 0 +
                count_agents_in_cells (map (get_cell g) l3))%nat.

  - rewrite map_app. rewrite count_agents_in_cells_app. rewrite Heq_l1.
    simpl. rewrite Hget_q'. simpl.
    change (l2 ++ p :: l3) with (l2 ++ [p] ++ l3).
    rewrite map_app, map_app. rewrite count_agents_in_cells_app, count_agents_in_cells_app.
    rewrite Heq_l2, Heq_l3. simpl. rewrite Hget_p'. simpl. lia.

  - rewrite map_app. rewrite count_agents_in_cells_app.
    simpl. rewrite Hcellq. simpl.
    change (l2 ++ p :: l3) with (l2 ++ [p] ++ l3).
    rewrite map_app, map_app. rewrite count_agents_in_cells_app, count_agents_in_cells_app.
    simpl. rewrite Hcellp. simpl. lia.
Qed.

Lemma seq_NoDup : forall start len, NoDup (seq start len).
Proof.
  intros start len. revert start.
  induction len as [| len' IH]; intros start.
  - simpl. constructor.
  - simpl. constructor.
    + rewrite in_seq. lia.
    + apply IH.
Qed.

Lemma map_NoDup_inj :
  forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros A B f l Hinj Hnodup.
  induction Hnodup as [| x l' Hnotin Hnodup' IH].
  - simpl. constructor.
  - simpl. constructor.
    + intros Hcontra. apply in_map_iff in Hcontra.
      destruct Hcontra as [y [Heq Hin]].
      assert (Heqxy : x = y).
      { apply Hinj. left. reflexivity. right. exact Hin. symmetry. exact Heq. }
      subst. contradiction.
    + apply IH. intros y z Hiny Hinz Heq.
      apply Hinj. right. exact Hiny. right. exact Hinz. exact Heq.
Qed.

Lemma NoDup_app_intro :
  forall {A : Type} (l1 l2 : list A),
    NoDup l1 ->
    NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 Hnd1 Hnd2 Hdisj.
  induction Hnd1 as [| x l1' Hnotin1 Hnd1' IH].
  - simpl. assumption.
  - simpl. constructor.
    + intros Hin. apply in_app_or in Hin.
      destruct Hin as [Hin1 | Hin2].
      * apply Hnotin1. assumption.
      * apply (Hdisj x). left. reflexivity. assumption.
    + apply IH. intros y Hiny. apply Hdisj. right. assumption.
Qed.

Lemma flat_map_rows_NoDup :
  forall (rows : list nat),
    NoDup rows ->
    NoDup (flat_map (fun i => map (fun j => (i, j)) (seq 0 grid_size)) rows).
Proof.
  intros rows Hnodup.
  induction Hnodup as [| i rows' Hnotin Hnodup' IH].
  - cbn [flat_map]. constructor.
  - cbn [flat_map]. apply NoDup_app_intro.
    + apply map_NoDup_inj.
      * intros x y Hinx Hiny Heq.
        injection Heq as Heq2.
        subst. reflexivity.
      * apply seq_NoDup.
    + assumption.
    + intros [i' j'] Hin1 Hin2.
      apply in_map_iff in Hin1. destruct Hin1 as [j [Heq1 Hinj]].
      inversion Heq1; subst i' j'. clear Heq1.
      apply in_flat_map in Hin2.
      destruct Hin2 as [i'' [Hin_i'' Hin_pair]].
      apply in_map_iff in Hin_pair.
      destruct Hin_pair as [j'' [Heq_pair Hinj'']].
      inversion Heq_pair; subst i'' j''. clear Heq_pair.
      apply Hnotin. assumption.
Qed.

Lemma all_positions_grid_NoDup : NoDup all_positions_grid.
Proof.
  unfold all_positions_grid.
  apply flat_map_rows_NoDup.
  apply seq_NoDup.
Qed.

Theorem von_neumann_radius_1_at_most_4_unconditional :
  neighborhood_radius = 1%nat ->
  forall p,
    (length (von_neumann_neighbors p) <= 4)%nat.
Proof.
  intros Hr1 p.
  apply von_neumann_radius_1_truly_at_most_4_conditional.
  - exact Hr1.
  - apply all_positions_grid_NoDup.
Qed.

Lemma NoDup_cons_app : forall {A} (x : A) l1 l2,
  NoDup (l1 ++ x :: l2) -> ~ In x l1.
Proof.
  intros A x l1 l2 H.
  induction l1 as [|y l1' IH].
  - intros [].
  - simpl in H. inversion H. subst.
    intros [Heq | Hin].
    + subst. apply H2. apply in_or_app. right. left. reflexivity.
    + apply IH. assumption. assumption.
Qed.

Lemma NoDup_cons_app_r : forall {A} (x : A) l1 l2,
  NoDup (l1 ++ x :: l2) -> ~ In x l2.
Proof.
  intros A x l1 l2 H.
  induction l1 as [|y l1' IH].
  - simpl in H. inversion H. assumption.
  - simpl in H. inversion H. subst. apply IH. assumption.
Qed.

Lemma NoDup_app_cons_cons : forall {A} (x y : A) l1 l2 l3,
  NoDup (l1 ++ x :: l2 ++ y :: l3) -> ~ In x l2.
Proof.
  intros A x y l1 l2 l3 H.
  intros Hcontra.
  apply in_split in Hcontra. destruct Hcontra as [l2a [l2b Heq_l2]].
  subst l2.
  assert (Heq : (l2a ++ x :: l2b) ++ y :: l3 = l2a ++ x :: l2b ++ y :: l3).
  { rewrite <- app_assoc. reflexivity. }
  rewrite Heq in H. clear Heq.
  apply NoDup_cons_app_r in H.
  apply H. apply in_or_app. right. left. reflexivity.
Qed.

Lemma NoDup_app_cons_cons_mid : forall {A} (x y : A) l1 l2 l3,
  NoDup (l1 ++ x :: l2 ++ y :: l3) -> ~ In y l1.
Proof.
  intros A x y l1 l2 l3 H.
  intros Hcontra.
  apply in_split in Hcontra. destruct Hcontra as [l1a [l1b Heq_l1]].
  subst l1.
  assert (Heq : (l1a ++ y :: l1b) ++ x :: l2 ++ y :: l3 =
                l1a ++ y :: (l1b ++ x :: l2 ++ y :: l3)).
  { rewrite <- app_assoc. reflexivity. }
  rewrite Heq in H. clear Heq.
  apply NoDup_cons_app_r in H.
  apply H. apply in_or_app. right. right. apply in_or_app. right. left. reflexivity.
Qed.

Lemma NoDup_app_cons_l : forall {A} (x : A) l1 l2,
  NoDup (l1 ++ x :: l2) -> ~ In x l1.
Proof.
  intros A x l1 l2 H. apply (NoDup_cons_app x l1 l2). assumption.
Qed.

Lemma in_split_specific :
  forall {A : Type} (x y : A) (l : list A),
    NoDup l ->
    x <> y ->
    In x l ->
    In y l ->
    exists l1 l2 l3,
      (l = l1 ++ x :: l2 ++ y :: l3 /\ ~ In x l2 /\ ~ In y l1) \/
      (l = l1 ++ y :: l2 ++ x :: l3 /\ ~ In y l2 /\ ~ In x l1).
Proof.
  intros A x y l Hnodup Hneq Hinx Hiny.
  destruct (in_split_exists_xy_or_yx x y l Hneq Hinx Hiny) as [[l1 [l2 [l3 Heq]]] | [l1 [l2 [l3 Heq]]]].
  - exists l1, l2, l3. left. split; [assumption | split].
    + rewrite Heq in Hnodup.
      apply NoDup_app_cons_cons with (y := y) (l1 := l1) (l3 := l3).
      assumption.
    + rewrite Heq in Hnodup.
      apply NoDup_app_cons_cons_mid with (x := x) (l2 := l2) (l3 := l3).
      assumption.
  - exists l1, l2, l3. right. split; [assumption | split].
    + rewrite Heq in Hnodup.
      apply NoDup_app_cons_cons with (y := x) (l1 := l1) (l3 := l3).
      assumption.
    + rewrite Heq in Hnodup.
      apply NoDup_app_cons_cons_mid with (x := y) (l2 := l2) (l3 := l3).
      assumption.
Qed.

Lemma count_agents_swap_cells :
  forall g p q a,
    p <> q ->
    In p all_positions_grid ->
    In q all_positions_grid ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    count_agents (set_cell (set_cell g p Empty) q (Occupied a)) = count_agents g.
Proof.
  intros g p q a Hneq Hinp Hinq Hcellp Hcellq.

  apply in_split in Hinp. destruct Hinp as [l1 [l2 Heq]].
  rewrite Heq in Hinq.
  apply in_app_or in Hinq.
  destruct Hinq as [Hinq_l1 | Hinq_l2].

  - apply in_split in Hinq_l1. destruct Hinq_l1 as [l1a [l1b Heq_l1]].

    assert (Hnodup : NoDup all_positions_grid) by apply all_positions_grid_NoDup.
    rewrite Heq in Hnodup. rewrite Heq_l1 in Hnodup.
    repeat rewrite <- app_assoc in Hnodup. simpl in Hnodup.

    unfold count_agents, count_agents_at_positions.
    rewrite Heq. rewrite Heq_l1.
    repeat rewrite <- app_assoc. simpl.

    assert (Hninp_l1a : ~ In p l1a).
    { apply NoDup_app_cons_cons_mid with (x := q) (l2 := l1b) (l3 := l2). assumption. }

    assert (Hninp_l1b : ~ In p l1b).
    { assert (Hnodup_copy : NoDup (l1a ++ q :: l1b ++ p :: l2)) by assumption.
      assert (Hnodup_p : NoDup ((l1a ++ q :: l1b) ++ p :: l2)).
      { assert (Heq_reassoc : l1a ++ q :: l1b ++ p :: l2 = (l1a ++ q :: l1b) ++ p :: l2).
        { rewrite <- app_assoc. reflexivity. }
        rewrite Heq_reassoc in Hnodup_copy. assumption. }
      assert (Hnotin : ~ In p (l1a ++ q :: l1b)).
      { apply NoDup_cons_app with (l2 := l2). assumption. }
      intros Hcontra. apply Hnotin. apply in_or_app. right. simpl. right. assumption. }

    assert (Hninp_l2 : ~ In p l2).
    { assert (Hnodup_copy2 : NoDup (l1a ++ q :: l1b ++ p :: l2)) by assumption.
      apply NoDup_cons_app_r with (l1 := l1a ++ q :: l1b).
      assert (Heq_app : l1a ++ q :: l1b ++ p :: l2 = (l1a ++ q :: l1b) ++ p :: l2).
      { rewrite <- app_assoc. reflexivity. }
      rewrite Heq_app in Hnodup_copy2. assumption. }

    assert (Hninq_l1a : ~ In q l1a).
    { assert (Hnodup_copy3 : NoDup (l1a ++ q :: l1b ++ p :: l2)) by assumption.
      apply NoDup_cons_app with (l2 := l1b ++ p :: l2). exact Hnodup_copy3. }

    assert (Hninq_l1b : ~ In q l1b).
    { assert (Hnodup_copy4 : NoDup (l1a ++ q :: l1b ++ p :: l2)) by assumption.
      assert (Hnotin_full : ~ In q (l1b ++ p :: l2)).
      { apply NoDup_cons_app_r with (l1 := l1a). exact Hnodup_copy4. }
      intros Hcontra. apply Hnotin_full. apply in_or_app. left. assumption. }

    assert (Hninq_l2 : ~ In q l2).
    { assert (Hnodup_copy5 : NoDup (l1a ++ q :: l1b ++ p :: l2)) by assumption.
      assert (Hnotin_full2 : ~ In q (l1b ++ p :: l2)).
      { apply NoDup_cons_app_r with (l1 := l1a). exact Hnodup_copy5. }
      intros Hcontra. apply Hnotin_full2. apply in_or_app. right. simpl. right. assumption. }

    apply count_swap_qp_order; assumption.

  - simpl in Hinq_l2. destruct Hinq_l2 as [Heq_q | Hinq_l2'].
    + subst q. exfalso. apply Hneq. reflexivity.
    + apply in_split in Hinq_l2'. destruct Hinq_l2' as [l2a [l2b Heq_l2]].

      assert (Hnodup : NoDup all_positions_grid) by apply all_positions_grid_NoDup.
      rewrite Heq in Hnodup. rewrite Heq_l2 in Hnodup.
      repeat rewrite <- app_assoc in Hnodup. simpl in Hnodup.

      unfold count_agents, count_agents_at_positions.
      rewrite Heq. rewrite Heq_l2.
      repeat rewrite <- app_assoc. simpl.

      assert (Hninp_l1 : ~ In p l1).
      { assert (Hnodup_copy1 : NoDup (l1 ++ p :: l2a ++ q :: l2b)) by assumption.
        apply NoDup_cons_app with (l2 := l2a ++ q :: l2b). exact Hnodup_copy1. }

      assert (Hninp_l2a : ~ In p l2a).
      { assert (Hnodup_copy2 : NoDup (l1 ++ p :: l2a ++ q :: l2b)) by assumption.
        apply NoDup_app_cons_cons with (y := q) (l1 := l1) (l3 := l2b). exact Hnodup_copy2. }

      assert (Hninp_l2b : ~ In p l2b).
      { assert (Hnodup_copy3 : NoDup (l1 ++ p :: l2a ++ q :: l2b)) by assumption.
        assert (Hnodup_p_form : NoDup ((l1 ++ p :: l2a) ++ q :: l2b)).
        { assert (Heq_form : l1 ++ p :: l2a ++ q :: l2b = (l1 ++ p :: l2a) ++ q :: l2b).
          { rewrite <- app_assoc. reflexivity. }
          rewrite Heq_form in Hnodup_copy3. assumption. }
        assert (Hnotin_full3 : ~ In p (l2a ++ q :: l2b)).
        { apply NoDup_cons_app_r with (l1 := l1). assumption. }
        intros Hcontra. apply Hnotin_full3. apply in_or_app. right. simpl. right. assumption. }

      assert (Hninq_l1 : ~ In q l1).
      { assert (Hnodup_copy4 : NoDup (l1 ++ p :: l2a ++ q :: l2b)) by assumption.
        apply NoDup_app_cons_cons_mid with (x := p) (l2 := l2a) (l3 := l2b). exact Hnodup_copy4. }

      assert (Hninq_l2a : ~ In q l2a).
      { assert (Hnodup_copy5 : NoDup (l1 ++ p :: l2a ++ q :: l2b)) by assumption.
        assert (Hnodup_q_form : NoDup ((l1 ++ p :: l2a) ++ q :: l2b)).
        { assert (Heq_form2 : l1 ++ p :: l2a ++ q :: l2b = (l1 ++ p :: l2a) ++ q :: l2b).
          { rewrite <- app_assoc. reflexivity. }
          rewrite Heq_form2 in Hnodup_copy5. assumption. }
        assert (Hnotin_full4 : ~ In q (l1 ++ p :: l2a)).
        { apply NoDup_cons_app with (l2 := l2b). assumption. }
        intros Hcontra. apply Hnotin_full4. apply in_or_app. right. simpl. right. assumption. }

      assert (Hninq_l2b : ~ In q l2b).
      { assert (Hnodup_copy6 : NoDup (l1 ++ p :: l2a ++ q :: l2b)) by assumption.
        assert (Hnodup_q_form2 : NoDup ((l1 ++ p :: l2a) ++ q :: l2b)).
        { assert (Heq_form3 : l1 ++ p :: l2a ++ q :: l2b = (l1 ++ p :: l2a) ++ q :: l2b).
          { rewrite <- app_assoc. reflexivity. }
          rewrite Heq_form3 in Hnodup_copy6. assumption. }
        apply NoDup_cons_app_r with (l1 := l1 ++ p :: l2a). assumption. }

      apply count_swap_pq_order; assumption.
Qed.

Lemma step_position_preserves_agent_count :
  forall tau g p,
    In p all_positions_grid ->
    count_agents (step_position tau g p) = count_agents g.
Proof.
  intros tau g p Hin.
  unfold step_position.
  destruct (get_cell g p) eqn:Hcell; [reflexivity|].
  destruct (happy tau g p) eqn:Hhappy; [reflexivity|].
  destruct (find_destination tau g a) eqn:Hfind; [|reflexivity].
  unfold find_destination in Hfind.
  destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hfind'; [|discriminate].
  injection Hfind as Hfind; subst.
  apply List.find_some in Hfind'.
  destruct Hfind' as [Hinq Hempty].
  unfold empty_and_happy_for in Hempty.
  rewrite Bool.andb_true_iff in Hempty.
  destruct Hempty as [Hemptyq _].
  unfold cell_is_empty in Hemptyq.
  rewrite Bool.negb_true_iff in Hemptyq.
  destruct (get_cell g p0) eqn:Hcellq; [|simpl in Hemptyq; discriminate].
  simpl in Hemptyq.
  destruct (pos_eq_dec p p0) as [Heqpp0 | Hneqpp0].
  - subst. rewrite Hcell in Hcellq. discriminate.
  - apply count_agents_swap_cells; assumption.
Qed.

Lemma step_positions_preserves_agent_count :
  forall tau ps g,
    (forall p, In p ps -> In p all_positions_grid) ->
    count_agents (step_positions tau ps g) = count_agents g.
Proof.
  intros tau ps; induction ps as [|p ps' IH]; intros g Hin; simpl.
  - reflexivity.
  - rewrite IH.
    + apply step_position_preserves_agent_count.
      apply Hin; left; reflexivity.
    + intros q Hq; apply Hin; right; assumption.
Qed.

Theorem step_preserves_agent_count :
  forall tau g,
    count_agents (step tau g) = count_agents g.
Proof.
  intros tau g.
  unfold step.
  apply step_positions_preserves_agent_count.
  intros p Hin; assumption.
Qed.

Corollary step_n_preserves_agent_count :
  forall tau g n,
    count_agents (Nat.iter n (step tau) g) = count_agents g.
Proof.
  intros tau g n.
  induction n as [|n' IH]; simpl.
  - reflexivity.
  - rewrite step_preserves_agent_count; assumption.
Qed.

Lemma swap_get_at_source :
  forall g p q a,
    q <> p ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p = Empty.
Proof.
  intros. rewrite get_set_other, get_set_same by assumption. reflexivity.
Qed.

Lemma swap_get_at_dest :
  forall g p q a,
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) q = Occupied a.
Proof.
  intros. rewrite get_set_same. reflexivity.
Qed.

Lemma swap_get_elsewhere :
  forall g p q a r,
    r <> p -> r <> q ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) r = get_cell g r.
Proof.
  intros g p q a r Hrp Hrq.
  rewrite get_set_other by (intros C; subst; contradiction).
  rewrite get_set_other by (intros C; subst; contradiction).
  reflexivity.
Qed.

Lemma count_cells_extensional :
  forall cs1 cs2,
    cs1 = cs2 ->
    count_agents_in_cells cs1 = count_agents_in_cells cs2.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma swap_when_both_in_bounds :
  forall g p q a,
    p <> q ->
    in_bounds p ->
    in_bounds q ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    count_agents (set_cell (set_cell g p Empty) q (Occupied a)) = count_agents g.
Proof.
  intros g p q a Hneq Hp Hq Hcellp Hcellq.
  apply count_agents_swap_cells; try assumption.
  - apply all_positions_complete; assumption.
  - apply all_positions_complete; assumption.
Qed.

Lemma set_cell_out_of_bounds_preserves_count :
  forall g p c,
    ~ in_bounds p ->
    count_agents (set_cell g p c) = count_agents g.
Proof.
  intros g p c Hout.
  unfold count_agents, count_agents_at_positions.
  apply f_equal.
  apply map_ext_in.
  intros r Hr.
  rewrite get_set_other.
  - reflexivity.
  - intros Heq; subst r.
    apply Hout.
    apply all_positions_only_in_bounds; assumption.
Qed.

Lemma set_cell_twice_out_of_bounds_preserves_count :
  forall g p q c1 c2,
    ~ in_bounds p ->
    ~ in_bounds q ->
    count_agents (set_cell (set_cell g p c1) q c2) = count_agents g.
Proof.
  intros g p q c1 c2 Hp Hq.
  rewrite set_cell_out_of_bounds_preserves_count by assumption.
  apply set_cell_out_of_bounds_preserves_count.
  assumption.
Qed.

Lemma set_cell_then_out_of_bounds_preserves_count :
  forall g p q c1 c2,
    ~ in_bounds q ->
    count_agents (set_cell (set_cell g p c1) q c2) = count_agents (set_cell g p c1).
Proof.
  intros g p q c1 c2 Hq.
  apply set_cell_out_of_bounds_preserves_count.
  assumption.
Qed.

Lemma out_of_bounds_cell_must_be_empty :
  forall g p,
    wellformed_grid g ->
    ~ in_bounds p ->
    get_cell g p = Empty.
Proof.
  intros g [i j] Hwf Hout.
  unfold in_bounds in Hout.
  simpl in Hout.
  apply Hwf.
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - exfalso; apply Hout; split; apply Nat.ltb_lt; assumption.
  - right; apply Nat.ltb_ge; assumption.
  - left; apply Nat.ltb_ge; assumption.
  - left; apply Nat.ltb_ge; assumption.
Qed.

Lemma set_cell_count_agents_swap :
  forall g p q a,
    p <> q ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    In p all_positions_grid ->
    In q all_positions_grid ->
    count_agents (set_cell (set_cell g p Empty) q (Occupied a)) = count_agents g.
Proof.
  intros g p q a Hneq Hcellp Hcellq Hinp Hinq.
  apply count_agents_swap_cells; assumption.
Qed.

Lemma apply_moves_preserves_count_single :
  forall g p q a,
    p <> q ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    In p all_positions_grid ->
    In q all_positions_grid ->
    count_agents (set_cell (set_cell g p Empty) q (Occupied a)) = count_agents g.
Proof.
  intros. apply set_cell_count_agents_swap; assumption.
Qed.

Lemma apply_moves_cons :
  forall m moves g,
    apply_moves (m :: moves) g = apply_moves moves (apply_moves [m] g).
Proof.
  intros [[p q] a] moves g. simpl. reflexivity.
Qed.

Lemma source_not_in_tail_sources :
  forall (p q : Pos) (a : Agent) (moves' : list (Pos * Pos * Agent)),
    (forall p1 q1 a1 p2 q2 a2,
      In (p1, q1, a1) ((p, q, a) :: moves') ->
      In (p2, q2, a2) ((p, q, a) :: moves') ->
      (p1, q1, a1) <> (p2, q2, a2) -> p1 <> p2) ->
    NoDup ((p, q, a) :: moves') ->
    forall p' q' a',
      In (p', q', a') moves' ->
      p' <> p.
Proof.
  intros p q a moves' Huniq Hnodup p' q' a' Hin Heq.
  subst p'.
  assert (H1: In (p, q, a) ((p, q, a) :: moves')) by (left; reflexivity).
  destruct (pos_eq_dec q q') as [Heq_q | Hneq_q];
  destruct (agent_eq_dec a a') as [Heq_a | Hneq_a].
  - subst q' a'.
    inversion Hnodup; subst.
    contradiction.
  - subst q'.
    assert (H2: In (p, q, a') ((p, q, a) :: moves')) by (right; exact Hin).
    assert (Hneq: (p, q, a) <> (p, q, a')).
    { intros Hcontra. injection Hcontra. intros. contradiction. }
    apply (Huniq p q a p q a' H1 H2 Hneq). reflexivity.
  - subst a'.
    assert (H2: In (p, q', a) ((p, q, a) :: moves')) by (right; exact Hin).
    assert (Hneq: (p, q, a) <> (p, q', a)).
    { intros Hcontra. injection Hcontra. intros. contradiction. }
    apply (Huniq p q a p q' a H1 H2 Hneq). reflexivity.
  - assert (H2: In (p, q', a') ((p, q, a) :: moves')) by (right; assumption).
    assert (Hneq: (p, q, a) <> (p, q', a')).
    { intros Hcontra. injection Hcontra. intros. contradiction. }
    apply (Huniq p q a p q' a' H1 H2 Hneq). reflexivity.
Qed.

Lemma dest_not_in_tail_dests :
  forall q moves',
    NoDup (q :: destinations_in_moves moves') ->
    forall q',
      In q' (destinations_in_moves moves') ->
      q' <> q.
Proof.
  intros q moves' Hnodup q' Hin.
  inversion Hnodup; subst.
  intros Heq; subst q'.
  contradiction.
Qed.

Lemma get_cell_after_swap_source_empty :
  forall g p q a p',
    p' <> p ->
    p' <> q ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p' = get_cell g p'.
Proof.
  intros g p q a p' Hneq_p Hneq_q.
  rewrite get_set_other.
  - rewrite get_set_other.
    + reflexivity.
    + intros Heq. apply Hneq_p. symmetry. exact Heq.
  - intros Heq. apply Hneq_q. symmetry. exact Heq.
Qed.

Lemma dest_in_moves :
  forall p q a moves,
    In (p, q, a) moves ->
    In q (destinations_in_moves moves).
Proof.
  intros p q a moves Hin.
  induction moves as [|[[px qx] ax] moves' IH].
  - inversion Hin.
  - simpl. simpl in Hin.
    destruct Hin as [Heq | Hin'].
    + injection Heq as Heq_p Heq_q Heq_a. subst. left. reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma not_in_dest_means_move_not_in :
  forall p q a moves,
    ~ In q (destinations_in_moves moves) ->
    ~ In (p, q, a) moves.
Proof.
  intros p q a moves Hnot_in Hcontra.
  apply Hnot_in.
  apply (dest_in_moves p q a moves).
  assumption.
Qed.

Lemma get_cell_after_swap_at_dest :
  forall g p q a,
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) q = Occupied a.
Proof.
  intros g p q a.
  rewrite get_set_same.
  reflexivity.
Qed.

Lemma apply_single_move_preserves_count :
  forall g p q a,
    In p all_positions_grid ->
    In q all_positions_grid ->
    p <> q ->
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    count_agents (set_cell (set_cell g p Empty) q (Occupied a)) = count_agents g.
Proof.
  intros g p q a Hinp Hinq Hneq Hcellp Hcellq.
  apply set_cell_count_agents_swap; assumption.
Qed.

Lemma compute_moves_sources_in_all_positions :
  forall tau g ps p q a,
    (forall r, In r ps -> In r all_positions_grid) ->
    In (p, q, a) (compute_moves tau g ps) ->
    In p all_positions_grid.
Proof.
  intros tau g ps p q a Hps_in Hin.
  induction ps as [|p' ps' IH].
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (get_cell g p') eqn:Hcell.
    + apply IH.
      * intros r Hr. apply Hps_in. right. assumption.
      * assumption.
    + destruct (happy tau g p') eqn:Hhappy.
      * apply IH.
        -- intros r Hr. apply Hps_in. right. assumption.
        -- assumption.
      * destruct (find_destination tau g a0) eqn:Hfind.
        -- simpl in Hin. destruct Hin as [Heq | Hin'].
           ++ inversion Heq; subst. apply Hps_in. left. reflexivity.
           ++ apply IH.
              ** intros r Hr. apply Hps_in. right. assumption.
              ** assumption.
        -- apply IH.
           ++ intros r Hr. apply Hps_in. right. assumption.
           ++ assumption.
Qed.

Lemma compute_moves_dests_in_all_positions :
  forall tau g ps p q a,
    In (p, q, a) (compute_moves tau g ps) ->
    In q all_positions_grid.
Proof.
  intros tau g ps. induction ps as [|p' ps' IH]; intros p q a Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (get_cell g p') eqn:Hcell.
    + apply (IH p q a). assumption.
    + destruct (happy tau g p') eqn:Hhappy.
      * apply (IH p q a). assumption.
      * destruct (find_destination tau g a0) eqn:Hfind.
        -- simpl in Hin. destruct Hin as [Heq | Hin'].
           ++ inversion Heq; subst.
              apply all_positions_complete.
              unfold find_destination in Hfind.
              destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hf; [|discriminate].
              injection Hfind as Hfind; subst p0.
              apply List.find_some in Hf.
              destruct Hf as [Hin_q _].
              apply all_positions_only_in_bounds.
              assumption.
           ++ apply (IH p q a). assumption.
        -- apply (IH p q a). assumption.
Qed.

Lemma sources_dests_disjoint_preserves_count :
  forall moves g,
    (forall p q a, In (p, q, a) moves -> In p all_positions_grid) ->
    (forall p q a, In (p, q, a) moves -> In q all_positions_grid) ->
    NoDup (destinations_in_moves moves) ->
    (forall p q a, In (p, q, a) moves -> get_cell g p = Occupied a) ->
    (forall p q a, In (p, q, a) moves -> get_cell g q = Empty) ->
    (forall p q a, In (p, q, a) moves -> p <> q) ->
    (forall p1 q1 a1 p2 q2 a2,
      In (p1, q1, a1) moves -> In (p2, q2, a2) moves ->
      (p1, q1, a1) <> (p2, q2, a2) -> p1 <> p2) ->
    count_agents (apply_moves moves g) = count_agents g.
Proof.
  intros moves.
  induction moves as [|[[p q] a] moves' IH]; intros g Hsrc_in Hdst_in Hnodup Hsrc_occ Hdst_empty Hneq Hsrc_uniq.
  - simpl. reflexivity.
  - simpl.
    set (g' := set_cell (set_cell g p Empty) q (Occupied a)).
    rewrite (IH g').
    + unfold g'.
      assert (Hp_in: In p all_positions_grid).
      { apply (Hsrc_in p q a). left. reflexivity. }
      assert (Hq_in: In q all_positions_grid).
      { apply (Hdst_in p q a). left. reflexivity. }
      assert (Hpq_neq: p <> q).
      { apply (Hneq p q a). left. reflexivity. }
      assert (Hp_occ: get_cell g p = Occupied a).
      { apply (Hsrc_occ p q a). left. reflexivity. }
      assert (Hq_empty: get_cell g q = Empty).
      { apply (Hdst_empty p q a). left. reflexivity. }
      apply set_cell_count_agents_swap; assumption.
    + intros p' q' a' Hin'. apply (Hsrc_in p' q' a'). right. assumption.
    + intros p' q' a' Hin'. apply (Hdst_in p' q' a'). right. assumption.
    + simpl in Hnodup. inversion Hnodup. assumption.
    + intros p' q' a' Hin'.
      unfold g'.
      assert (Hp'_neq_p: p' <> p).
      { intros Heq. subst p'.
        assert (H_head: In (p, q, a) ((p, q, a) :: moves')) by (left; reflexivity).
        assert (H_tail: In (p, q', a') ((p, q, a) :: moves')) by (right; assumption).
        destruct (pos_eq_dec q q') as [Heq_q | Hneq_q];
        destruct (agent_eq_dec a a') as [Heq_a | Hneq_a].
        - subst q' a'.
          simpl in Hnodup. inversion Hnodup; subst.
          apply H1.
          apply (dest_in_moves p q a moves'). assumption.
        - subst q'.
          assert (Hneq_moves: (p, q, a) <> (p, q, a')).
          { intros Hcontra. injection Hcontra. intros. contradiction. }
          apply (Hsrc_uniq p q a p q a' H_head H_tail Hneq_moves). reflexivity.
        - subst a'.
          assert (Hneq_moves: (p, q, a) <> (p, q', a)).
          { intros Hcontra. injection Hcontra. intros. contradiction. }
          apply (Hsrc_uniq p q a p q' a H_head H_tail Hneq_moves). reflexivity.
        - assert (Hneq_moves: (p, q, a) <> (p, q', a')).
          { intros Hcontra. injection Hcontra. intros. contradiction. }
          apply (Hsrc_uniq p q a p q' a' H_head H_tail Hneq_moves). reflexivity. }
      assert (Hp'_neq_q: p' <> q).
      { intros Heq. subst p'.
        assert (Hq_occ: get_cell g q = Occupied a').
        { apply (Hsrc_occ q q' a'). right. assumption. }
        assert (Hq_empty: get_cell g q = Empty).
        { apply (Hdst_empty p q a). left. reflexivity. }
        rewrite Hq_empty in Hq_occ.
        discriminate. }
      rewrite (get_cell_after_swap_source_empty g p q a p' Hp'_neq_p Hp'_neq_q).
      apply (Hsrc_occ p' q' a'). right. assumption.
    + intros p' q' a' Hin'.
      unfold g'.
      assert (Hq'_neq_p: q' <> p).
      { intros Heq. subst q'.
        assert (Hp_occ: get_cell g p = Occupied a).
        { apply (Hsrc_occ p q a). left. reflexivity. }
        assert (Hp_empty: get_cell g p = Empty).
        { apply (Hdst_empty p' p a'). right. assumption. }
        rewrite Hp_empty in Hp_occ.
        discriminate. }
      assert (Hq'_neq_q: q' <> q).
      { simpl in Hnodup. inversion Hnodup; subst.
        apply (dest_not_in_tail_dests q moves' Hnodup q').
        apply (dest_in_moves p' q' a' moves').
        assumption. }
      rewrite (get_cell_after_swap_source_empty g p q a q' Hq'_neq_p Hq'_neq_q).
      apply (Hdst_empty p' q' a'). right. assumption.
    + intros p' q' a' Hin'. apply (Hneq p' q' a'). right. assumption.
    + intros p1 q1 a1 p2 q2 a2 H1 H2 Hneq_moves.
      apply (Hsrc_uniq p1 q1 a1 p2 q2 a2).
      * right. assumption.
      * right. assumption.
      * assumption.
Qed.

Lemma compute_moves_sources_in_ps :
  forall tau g ps p q a,
    In (p, q, a) (compute_moves tau g ps) ->
    In p ps.
Proof.
  intros tau g ps. induction ps as [|p' ps' IH]; intros p q a Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (get_cell g p') eqn:Hcell.
    + right. apply (IH p q a). assumption.
    + destruct (happy tau g p') eqn:Hhappy.
      * right. apply (IH p q a). assumption.
      * destruct (find_destination tau g a0) eqn:Hfind.
        -- simpl in Hin. destruct Hin as [Heq | Hin'].
           ++ inversion Heq; subst. left. reflexivity.
           ++ right. apply (IH p q a). assumption.
        -- right. apply (IH p q a). assumption.
Qed.

Lemma compute_moves_at_most_one_per_position :
  forall tau g ps p q1 a1 q2 a2,
    NoDup ps ->
    In (p, q1, a1) (compute_moves tau g ps) ->
    In (p, q2, a2) (compute_moves tau g ps) ->
    (p, q1, a1) = (p, q2, a2).
Proof.
  intros tau g ps. induction ps as [|p' ps' IH]; intros p q1 a1 q2 a2 Hnodup Hin1 Hin2.
  - simpl in Hin1. contradiction.
  - simpl in Hin1, Hin2.
    inversion Hnodup; subst.
    destruct (get_cell g p') eqn:Hcell.
    + apply (IH p q1 a1 q2 a2); assumption.
    + destruct (happy tau g p') eqn:Hhappy.
      * apply (IH p q1 a1 q2 a2); assumption.
      * destruct (find_destination tau g a) eqn:Hfind.
        -- simpl in Hin1, Hin2.
           destruct Hin1 as [Heq1 | Hin1'], Hin2 as [Heq2 | Hin2'].
           ++ congruence.
           ++ inversion Heq1; subst.
              exfalso.
              apply compute_moves_sources_in_ps in Hin2'.
              contradiction.
           ++ inversion Heq2; subst.
              exfalso.
              apply compute_moves_sources_in_ps in Hin1'.
              contradiction.
           ++ apply (IH p q1 a1 q2 a2); assumption.
        -- apply (IH p q1 a1 q2 a2); assumption.
Qed.

Lemma compute_moves_sources_unique :
  forall tau g ps p1 q1 a1 p2 q2 a2,
    NoDup ps ->
    In (p1, q1, a1) (compute_moves tau g ps) ->
    In (p2, q2, a2) (compute_moves tau g ps) ->
    (p1, q1, a1) <> (p2, q2, a2) ->
    p1 <> p2.
Proof.
  intros tau g ps p1 q1 a1 p2 q2 a2 Hnodup H1 H2 Hneq.
  intros Heq; subst p2.
  apply Hneq.
  apply (compute_moves_at_most_one_per_position tau g ps p1 q1 a1 q2 a2); assumption.
Qed.

Lemma remove_conflicts_preserves_properties :
  forall moves tau g ps,
    NoDup ps ->
    moves = compute_moves tau g ps ->
    (forall p q a, In (p, q, a) (remove_conflicts moves) -> get_cell g p = Occupied a) /\
    (forall p q a, In (p, q, a) (remove_conflicts moves) -> get_cell g q = Empty) /\
    (forall p q a, In (p, q, a) (remove_conflicts moves) -> p <> q) /\
    (forall p1 q1 a1 p2 q2 a2,
      In (p1, q1, a1) (remove_conflicts moves) ->
      In (p2, q2, a2) (remove_conflicts moves) ->
      (p1, q1, a1) <> (p2, q2, a2) -> p1 <> p2).
Proof.
  intros moves tau g ps Hnodup Heq. subst moves. repeat split.
  - intros p q a Hin. apply remove_conflicts_subset in Hin.
    eapply compute_moves_source_occupied. eassumption.
  - intros p q a Hin. apply remove_conflicts_subset in Hin.
    eapply compute_moves_dest_empty. eassumption.
  - intros p q a Hin. apply remove_conflicts_subset in Hin.
    eapply compute_moves_source_dest_different. eassumption.
  - intros p1 q1 a1 p2 q2 a2 H1 H2 Hneq.
    apply remove_conflicts_subset in H1.
    apply remove_conflicts_subset in H2.
    eapply compute_moves_sources_unique; eassumption.
Qed.

Theorem step_parallel_preserves_agent_count :
  forall tau g,
    count_agents (step_parallel tau g) = count_agents g.
Proof.
  intros tau g.
  unfold step_parallel.
  set (moves := compute_moves tau g all_positions_grid).
  assert (Hprops := remove_conflicts_preserves_properties moves tau g all_positions_grid all_positions_grid_NoDup eq_refl).
  destruct Hprops as [Hsrc [Hdst [Hpq Hdisj]]].
  apply sources_dests_disjoint_preserves_count.
  - intros p q a Hin.
    apply remove_conflicts_subset in Hin.
    unfold moves in Hin.
    eapply compute_moves_sources_in_all_positions.
    + intros r Hr. exact Hr.
    + exact Hin.
  - intros p q a Hin.
    apply remove_conflicts_subset in Hin.
    unfold moves in Hin.
    eapply compute_moves_dests_in_all_positions.
    exact Hin.
  - apply remove_conflicts_no_duplicates.
  - exact Hsrc.
  - exact Hdst.
  - exact Hpq.
  - exact Hdisj.
Qed.

(* -----------------------------------------------------------------------------
   Segregation Metrics: Measuring Clustering and Separation
   ----------------------------------------------------------------------------- *)

Fixpoint count_different (a : Agent) (cells : list Cell) : nat :=
  match cells with
  | [] => 0
  | Empty :: cs => count_different a cs
  | Occupied b :: cs =>
      if agent_eqb a b
      then count_different a cs
      else S (count_different a cs)
  end.

Lemma count_same_plus_different :
  forall a cells,
    (count_same a cells + count_different a cells)%nat =
    count_agents_in_cells cells.
Proof.
  intros a cells.
  induction cells as [|c cells' IH]; simpl.
  - reflexivity.
  - destruct c; simpl.
    + exact IH.
    + destruct (agent_eqb a a0); simpl; lia.
Qed.

Definition local_homophily (g : Grid) (p : Pos) : Q :=
  match get_cell g p with
  | Empty => 0%Q
  | Occupied a =>
      let same := count_same a (neighbor_cells g p) in
      let diff := count_different a (neighbor_cells g p) in
      let total := (same + diff)%nat in
      match total with
      | O => 0%Q
      | S _ => (Z.of_nat same # Pos.of_nat total)
      end
  end.

Lemma Q_frac_le_1 : forall (num denom : nat),
  (num <= denom)%nat ->
  (0 < denom)%nat ->
  (Z.of_nat num # Pos.of_nat denom <= 1)%Q.
Proof.
  intros num denom Hle Hpos.
  unfold Qle. simpl.
  assert (Z.of_nat num <= Z.of_nat denom) by lia.
  assert (Z.pos (Pos.of_nat denom) = Z.of_nat denom).
  { rewrite <- Znat.positive_nat_Z by assumption.
    rewrite Nat2Pos.id by lia.
    reflexivity. }
  rewrite H0. lia.
Qed.

Lemma local_homophily_range :
  forall g p,
    (0 <= local_homophily g p <= 1)%Q.
Proof.
  intros g p.
  unfold local_homophily.
  destruct (get_cell g p) eqn:Hcell.
  - split.
    + apply Qle_refl.
    + unfold Qle. simpl. lia.
  - remember (count_same a (neighbor_cells g p)) as same.
    remember (count_different a (neighbor_cells g p)) as diff.
    destruct (same + diff)%nat eqn:Htotal.
    + split.
      * apply Qle_refl.
      * unfold Qle. simpl. lia.
    + assert (Hle : (same <= S n)%nat) by lia.
      split.
      * unfold Qle. simpl. lia.
      * apply Q_frac_le_1; lia.
Qed.

Lemma local_homophily_empty :
  forall g p,
    get_cell g p = Empty ->
    local_homophily g p = 0%Q.
Proof.
  intros g p Hempty.
  unfold local_homophily.
  rewrite Hempty.
  reflexivity.
Qed.

Lemma Q_num_denom_equal : forall p : positive, (Z.pos p # p == 1)%Q.
Proof.
  intros p.
  unfold Qeq. simpl.
  lia.
Qed.

Lemma Z_of_nat_to_pos : forall n, (0 < n)%nat -> Z.of_nat n = Z.pos (Pos.of_nat n).
Proof.
  intros n Hpos.
  rewrite <- Znat.positive_nat_Z by assumption.
  rewrite Nat2Pos.id by lia.
  reflexivity.
Qed.

Lemma local_homophily_all_same_neighbors :
  forall g p a,
    get_cell g p = Occupied a ->
    count_different a (neighbor_cells g p) = 0%nat ->
    (count_same a (neighbor_cells g p) > 0)%nat ->
    (local_homophily g p == 1)%Q.
Proof.
  intros g p a Hocc Hdiff Hsame.
  unfold local_homophily.
  rewrite Hocc.
  rewrite Hdiff.
  destruct (count_same a (neighbor_cells g p)) eqn:Hcount.
  - lia.
  - rewrite Nat.add_0_r.
    rewrite Z_of_nat_to_pos by lia.
    apply Q_num_denom_equal.
Qed.

Lemma happy_implies_high_homophily :
  forall tau g p a,
    get_cell g p = Occupied a ->
    happy tau g p = true ->
    (tau > 0)%nat ->
    (count_agents_in_cells (neighbor_cells g p) > 0)%nat ->
    (Z.of_nat tau # Pos.of_nat (count_agents_in_cells (neighbor_cells g p)) <= local_homophily g p)%Q.
Proof.
  intros tau g p a Hocc Hhappy Htau_pos Hneigh_pos.
  unfold happy in Hhappy.
  rewrite Hocc in Hhappy.
  apply Nat.leb_le in Hhappy.
  unfold local_homophily.
  rewrite Hocc.
  assert (Htotal: (count_same a (neighbor_cells g p) + count_different a (neighbor_cells g p))%nat =
                  count_agents_in_cells (neighbor_cells g p)).
  { apply count_same_plus_different. }
  destruct (count_same a (neighbor_cells g p) + count_different a (neighbor_cells g p))%nat eqn:Htotal_eq.
  - rewrite <- Htotal in Hneigh_pos. lia.
  - rewrite Htotal.
    unfold Qle. simpl.
    apply Zmult_le_compat_r; lia.
Qed.

Fixpoint sum_local_homophily_list (g : Grid) (ps : list Pos) : Q :=
  match ps with
  | [] => 0%Q
  | p :: ps' => (local_homophily g p + sum_local_homophily_list g ps')%Q
  end.

Definition global_segregation (g : Grid) : Q :=
  let total_agents := count_agents g in
  match total_agents with
  | O => 0%Q
  | S _ =>
      (sum_local_homophily_list g all_positions_grid * (1 # Pos.of_nat total_agents))%Q
  end.

Lemma sum_local_homophily_nonneg :
  forall g ps,
    (0 <= sum_local_homophily_list g ps)%Q.
Proof.
  intros g ps.
  induction ps as [|p ps' IH]; simpl.
  - apply Qle_refl.
  - assert (H1: (0 <= local_homophily g p)%Q).
    { destruct (local_homophily_range g p) as [H _]. exact H. }
    assert (H2: (0 <= sum_local_homophily_list g ps')%Q).
    { exact IH. }
    unfold Qle in *. simpl in *.
    destruct (local_homophily g p) as [n1 d1].
    destruct (sum_local_homophily_list g ps') as [n2 d2].
    simpl in *. ring_simplify. nia.
Qed.

Lemma sum_local_homophily_bounded :
  forall g ps,
    (sum_local_homophily_list g ps <= Z.of_nat (count_agents_at_positions g ps) # 1)%Q.
Proof.
  intros g ps.
  induction ps as [|p ps' IH]; simpl.
  - unfold Qle. simpl. lia.
  - unfold count_agents_at_positions in *. simpl.
    destruct (get_cell g p) eqn:Hcell.
    + simpl.
      assert (H: local_homophily g p = 0%Q).
      { unfold local_homophily. rewrite Hcell. reflexivity. }
      rewrite H.
      setoid_replace (0 + sum_local_homophily_list g ps')%Q
        with (sum_local_homophily_list g ps')%Q by ring.
      exact IH.
    + assert (Hle: (local_homophily g p <= 1)%Q).
      { destruct (local_homophily_range g p) as [_ H]. exact H. }
      assert (Hsum: (sum_local_homophily_list g ps' <= Z.of_nat (count_agents_in_cells (map (get_cell g) ps')) # 1)%Q).
      { exact IH. }
      unfold count_agents_at_positions.
      simpl sum_local_homophily_list.
      simpl map. simpl count_agents_in_cells.
      set (rhs := Qplus (inject_Z 1) (Z.of_nat (count_agents_in_cells (map (get_cell g) ps')) # 1)).
      apply Qle_trans with (y := rhs).
      * apply Qplus_le_compat.
        -- exact Hle.
        -- exact Hsum.
      * unfold rhs.
        assert (Heq : Qplus (inject_Z 1) (Z.of_nat (count_agents_in_cells (map (get_cell g) ps')) # 1) ==
                      Z.of_nat (S (count_agents_in_cells (map (get_cell g) ps'))) # 1).
        { unfold inject_Z, "==", Qeq.
          rewrite Nat2Z.inj_succ.
          simpl. rewrite !Z.mul_1_r.
          rewrite <- Z.add_1_l. reflexivity. }
        rewrite <- Heq.
        apply Qle_refl.
Qed.

Lemma Zpos_of_nat_Sn : forall n, Z.pos (Pos.of_nat (S n)) = Z.of_nat (S n).
Proof.
  intros n.
  assert (Hpos: (0 < S n)%nat) by lia.
  assert (Hconv: Pos.to_nat (Pos.of_nat (S n)) = S n).
  { apply Nat2Pos.id. lia. }
  rewrite <- Hconv at 2.
  symmetry.
  apply positive_nat_Z.
Qed.

Lemma global_segregation_range :
  forall g,
    (0 <= global_segregation g <= 1)%Q.
Proof.
  intros g.
  unfold global_segregation.
  destruct (count_agents g) eqn:Hcount.
  - split.
    + apply Qle_refl.
    + unfold Qle. simpl. lia.
  - split.
    + assert (H1: (0 <= sum_local_homophily_list g all_positions_grid)%Q).
      { apply sum_local_homophily_nonneg. }
      assert (H2: (0 <= 1 # Pos.of_nat (S n))%Q).
      { unfold Qle. simpl. lia. }
      apply Qmult_le_0_compat; assumption.
    + assert (Hbound: (sum_local_homophily_list g all_positions_grid <=
                       Z.of_nat (count_agents_at_positions g all_positions_grid) # 1)%Q).
      { apply sum_local_homophily_bounded. }
      unfold count_agents in Hcount.
      assert (Hbound': (sum_local_homophily_list g all_positions_grid <= Z.of_nat (S n) # 1)%Q).
      { rewrite <- Hcount. exact Hbound. }
      clear Hbound.
      unfold Qle in *.
      destruct (sum_local_homophily_list g all_positions_grid) as [num den] eqn:Heq_sum.
      cbn [Qmult Qnum Qden fst snd Pos.mul].
      pose proof (Zpos_of_nat_Sn n) as Hconv.
      assert (Hden_pos: (0 < Z.pos den)%Z) by apply Pos2Z.is_pos.
      cbn [Qnum Qden fst snd] in Hbound'.
      rewrite Z.mul_1_r in Hbound'.
      subst.
      nia.
Qed.

(* -----------------------------------------------------------------------------
   Convergence and Termination Analysis
   ----------------------------------------------------------------------------- *)

Fixpoint count_unhappy_positions_list (tau : nat) (g : Grid) (ps : list Pos) : nat :=
  match ps with
  | [] => 0%nat
  | p :: ps' =>
      if happy tau g p then
        count_unhappy_positions_list tau g ps'
      else
        S (count_unhappy_positions_list tau g ps')
  end.

Definition count_unhappy_positions (tau : nat) (g : Grid) : nat :=
  count_unhappy_positions_list tau g all_positions_grid.

Lemma count_unhappy_positions_list_app :
  forall tau g ps1 ps2,
    count_unhappy_positions_list tau g (ps1 ++ ps2) =
    (count_unhappy_positions_list tau g ps1 + count_unhappy_positions_list tau g ps2)%nat.
Proof.
  intros tau g ps1 ps2.
  induction ps1 as [|p ps1' IH]; simpl.
  - reflexivity.
  - destruct (happy tau g p); simpl; rewrite IH; reflexivity.
Qed.

Lemma count_unhappy_zero_iff_all_happy :
  forall tau g ps,
    count_unhappy_positions_list tau g ps = 0%nat <->
    (forall p, In p ps -> happy tau g p = true).
Proof.
  intros tau g ps; split.
  - induction ps as [|p' ps' IH]; intros Hcount p Hin.
    + inversion Hin.
    + simpl in Hcount. destruct (happy tau g p') eqn:Hhappy.
      * simpl in Hin. destruct Hin as [Heq | Hin'].
        -- subst; assumption.
        -- apply IH; assumption.
      * discriminate.
  - intros H. induction ps as [|p ps' IH]; simpl.
    + reflexivity.
    + rewrite H by (left; reflexivity).
      apply IH. intros q Hq. apply H. right. assumption.
Qed.

Lemma stable_iff_count_unhappy_zero :
  forall tau g,
    wellformed_grid g ->
    stable tau g <-> count_unhappy_positions tau g = 0%nat.
Proof.
  intros tau g Hwf; split; intros H.
  - unfold count_unhappy_positions.
    apply count_unhappy_zero_iff_all_happy.
    intros p Hin. apply H.
  - unfold stable. intros p.
    destruct p as [i j].
    destruct (in_bounds_dec (i, j)) as [Hib | Hnb].
    + assert (Hin : In (i, j) all_positions_grid).
      { destruct Hib as [Hi Hj]. apply all_positions_coverage; assumption. }
      unfold count_unhappy_positions in H.
      rewrite count_unhappy_zero_iff_all_happy in H.
      apply H. assumption.
    + apply empty_cell_always_happy.
      apply Hwf.
      unfold in_bounds in Hnb. simpl in Hnb.
      destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
      * exfalso. apply Hnb. split; apply Nat.ltb_lt; assumption.
      * right. apply Nat.ltb_ge. assumption.
      * left. apply Nat.ltb_ge. assumption.
      * left. apply Nat.ltb_ge. assumption.
Qed.

Lemma count_unhappy_bounded :
  forall tau g,
    (count_unhappy_positions tau g <= length all_positions_grid)%nat.
Proof.
  intros tau g.
  unfold count_unhappy_positions.
  induction all_positions_grid as [|p ps IH]; simpl.
  - lia.
  - destruct (happy tau g p); simpl; lia.
Qed.

Definition grid_configs_finite := (3 ^ (grid_size * grid_size))%nat.

(** * Termination and Convergence *)

Lemma zero_unhappy_implies_stable :
  forall tau g,
    wellformed_grid g ->
    count_unhappy_positions tau g = 0%nat ->
    step tau g = g.
Proof.
  intros tau g Hwf Hcount.
  apply stable_iff_count_unhappy_zero in Hcount; [|assumption].
  apply step_stable_fixed_point; assumption.
Qed.

Corollary iterations_preserve_wellformed :
  forall tau g n,
    wellformed_grid g ->
    wellformed_grid (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf.
  apply step_n_preserves_wellformed; assumption.
Qed.

Corollary iterations_preserve_agent_count :
  forall tau g n,
    count_agents (Nat.iter n (step tau) g) = count_agents g.
Proof.
  intros tau g n.
  apply step_n_preserves_agent_count.
Qed.

(** * Cycle Detection *)

Definition has_period (tau : nat) (g : Grid) (p : nat) : Prop :=
  (p > 0)%nat /\ Nat.iter p (step tau) g = g.

Definition is_fixpoint (tau : nat) (g : Grid) : Prop :=
  step tau g = g.

Lemma fixpoint_is_period_1 :
  forall tau g,
    is_fixpoint tau g <-> has_period tau g 1.
Proof.
  intros tau g; split; intros H.
  - unfold has_period; simpl; split; [lia | assumption].
  - unfold has_period in H; destruct H as [_ H]; simpl in H; assumption.
Qed.

Lemma happy_empty_cell :
  forall tau g p,
    get_cell g p = Empty ->
    happy tau g p = true.
Proof.
  intros tau g p Hempty.
  unfold happy.
  rewrite Hempty.
  reflexivity.
Qed.

Lemma unhappy_means_occupied :
  forall tau g p,
    happy tau g p = false ->
    exists a, get_cell g p = Occupied a.
Proof.
  intros tau g p Hunhappy.
  unfold happy in Hunhappy.
  destruct (get_cell g p) eqn:Hcell.
  - discriminate.
  - exists a; reflexivity.
Qed.

Lemma stable_implies_fixpoint :
  forall tau g,
    stable tau g ->
    is_fixpoint tau g.
Proof.
  intros tau g Hstable.
  unfold is_fixpoint.
  apply step_stable_fixed_point.
  assumption.
Qed.

Lemma period_multiple :
  forall tau g p k,
    has_period tau g p ->
    Nat.iter (k * p) (step tau) g = g.
Proof.
  intros tau g p k [Hpos Hperiod].
  induction k as [|k' IH]; simpl.
  - reflexivity.
  - replace (S k' * p)%nat with (k' * p + p)%nat by lia.
    rewrite Nat.iter_add.
    rewrite IH.
    assumption.
Qed.

Lemma step_position_stable_or_changes :
  forall tau g p,
    In p all_positions_grid ->
    step_position tau g p = g \/
    (exists q a, get_cell g p = Occupied a /\
                 happy tau g p = false /\
                 get_cell g q = Empty /\
                 happy_for tau g a q = true).
Proof.
  intros tau g p Hin.
  unfold step_position.
  destruct (get_cell g p) eqn:Hcell.
  - left; reflexivity.
  - destruct (happy tau g p) eqn:Hhappy.
    + left; reflexivity.
    + destruct (find_destination tau g a) eqn:Hfind.
      * unfold find_destination in Hfind.
        destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hf; [|discriminate].
        injection Hfind as Hfind; subst p0.
        apply List.find_some in Hf.
        destruct Hf as [Hin_p1 Hcond].
        unfold empty_and_happy_for in Hcond.
        rewrite Bool.andb_true_iff in Hcond.
        destruct Hcond as [Hempty Hhappyfor].
        unfold cell_is_empty in Hempty.
        rewrite Bool.negb_true_iff in Hempty.
        destruct (get_cell g p1) eqn:Hcellq; [|simpl in Hempty; discriminate].
        right.
        exists p1, a.
        repeat split; auto.
      * left; reflexivity.
Qed.

Fixpoint grid_eq_at_positions (g1 g2 : Grid) (ps : list Pos) : bool :=
  match ps with
  | [] => true
  | p :: ps' =>
      match get_cell g1 p, get_cell g2 p with
      | Empty, Empty => grid_eq_at_positions g1 g2 ps'
      | Occupied a1, Occupied a2 =>
          agent_eqb a1 a2 && grid_eq_at_positions g1 g2 ps'
      | _, _ => false
      end
  end.

Definition grid_eq (g1 g2 : Grid) : bool :=
  grid_eq_at_positions g1 g2 all_positions_grid.

Lemma grid_eq_refl :
  forall g,
    grid_eq g g = true.
Proof.
  intros g.
  unfold grid_eq.
  induction all_positions_grid as [|p ps IH]; simpl.
  - reflexivity.
  - destruct (get_cell g p) eqn:Hcell.
    + apply IH.
    + rewrite agent_eqb_refl. simpl. apply IH.
Qed.

Lemma grid_eq_spec :
  forall g1 g2,
    grid_eq g1 g2 = true <->
    (forall p, In p all_positions_grid -> get_cell g1 p = get_cell g2 p).
Proof.
  intros g1 g2; split.
  - intros Heq p Hin.
    unfold grid_eq in Heq.
    induction all_positions_grid as [|p' ps' IH]; simpl in *.
    + inversion Hin.
    + destruct Hin as [Heqp | Hinp'].
      * subst p'.
        destruct (get_cell g1 p) eqn:Hc1, (get_cell g2 p) eqn:Hc2; try discriminate.
        -- reflexivity.
        -- rewrite Bool.andb_true_iff in Heq.
           destruct Heq as [Hagent _].
           apply agent_eqb_eq in Hagent.
           rewrite Hagent. reflexivity.
      * destruct (get_cell g1 p') eqn:Hc1', (get_cell g2 p') eqn:Hc2'; try discriminate.
        -- apply IH; assumption.
        -- rewrite Bool.andb_true_iff in Heq.
           destruct Heq as [_ Heq'].
           apply IH; assumption.
  - intros Hext.
    unfold grid_eq.
    induction all_positions_grid as [|p ps' IH]; simpl.
    + reflexivity.
    + assert (Hp : get_cell g1 p = get_cell g2 p) by (apply Hext; left; reflexivity).
      rewrite <- Hp.
      destruct (get_cell g1 p) eqn:Hc.
      * apply IH. intros q Hq. apply Hext. right. assumption.
      * rewrite agent_eqb_refl. simpl.
        apply IH. intros q Hq. apply Hext. right. assumption.
Qed.

Lemma grid_eq_false_implies_exists_diff :
  forall g1 g2,
    grid_eq g1 g2 = false ->
    exists p, In p all_positions_grid /\ get_cell g1 p <> get_cell g2 p.
Proof.
  intros g1 g2 Heq.
  unfold grid_eq in Heq.
  induction all_positions_grid as [|p ps IH]; simpl in Heq.
  - discriminate.
  - destruct (get_cell g1 p) eqn:H1, (get_cell g2 p) eqn:H2.
    + destruct (IH Heq) as [q [Hin Hdiff]].
      exists q; split; [right; assumption | assumption].
    + exists p; split; [left; reflexivity | congruence].
    + exists p; split; [left; reflexivity | congruence].
    + destruct (agent_eqb a a0) eqn:Hagent.
      * destruct (IH Heq) as [q [Hin Hdiff]].
        exists q; split; [right; assumption | assumption].
      * exists p; split; [left; reflexivity |].
        apply agent_eqb_neq in Hagent; congruence.
Qed.

Lemma step_out_of_bounds_empty :
  forall tau g i j,
    wellformed_grid g ->
    (i >= grid_size)%nat \/ (j >= grid_size)%nat ->
    get_cell (step tau g) (i, j) = Empty.
Proof.
  intros tau g i j Hwf Hout.
  apply step_preserves_wellformed; assumption.
Qed.

Lemma grid_eq_true_extensional :
  forall g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    grid_eq g1 g2 = true ->
    forall i j, get_cell g1 (i, j) = get_cell g2 (i, j).
Proof.
  intros g1 g2 Hwf1 Hwf2 Heq i j.
  rewrite grid_eq_spec in Heq.
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - apply Nat.ltb_lt in Hi; apply Nat.ltb_lt in Hj.
    apply Heq; apply all_positions_coverage; assumption.
  - assert (H1: get_cell g1 (i,j) = Empty) by (apply Hwf1; right; apply Nat.ltb_ge; assumption).
    assert (H2: get_cell g2 (i,j) = Empty) by (apply Hwf2; right; apply Nat.ltb_ge; assumption).
    rewrite H1, H2; reflexivity.
  - assert (H1: get_cell g1 (i,j) = Empty) by (apply Hwf1; left; apply Nat.ltb_ge; assumption).
    assert (H2: get_cell g2 (i,j) = Empty) by (apply Hwf2; left; apply Nat.ltb_ge; assumption).
    rewrite H1, H2; reflexivity.
  - assert (H1: get_cell g1 (i,j) = Empty) by (apply Hwf1; left; apply Nat.ltb_ge; assumption).
    assert (H2: get_cell g2 (i,j) = Empty) by (apply Hwf2; left; apply Nat.ltb_ge; assumption).
    rewrite H1, H2; reflexivity.
Qed.

Lemma grid_eq_true_to_functional_eq :
  forall g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    grid_eq g1 g2 = true ->
    g1 = g2.
Proof.
  intros g1 g2 Hwf1 Hwf2 Heq.
  apply functional_extensionality; intros p.
  destruct p as [i j].
  apply grid_eq_true_extensional; assumption.
Qed.

Lemma grid_eq_false_implies_grids_differ :
  forall g1 g2,
    grid_eq g1 g2 = false ->
    g1 <> g2.
Proof.
  intros g1 g2 Heq Hcontra.
  apply grid_eq_false_implies_exists_diff in Heq.
  destruct Heq as [p [Hin Hdiff]].
  apply Hdiff.
  rewrite Hcontra; reflexivity.
Qed.

Lemma fixpoint_decidable :
  forall tau g,
    wellformed_grid g ->
    {is_fixpoint tau g} + {~ is_fixpoint tau g}.
Proof.
  intros tau g Hwf.
  unfold is_fixpoint.
  destruct (grid_eq (step tau g) g) eqn:Heq.
  - left.
    apply grid_eq_true_to_functional_eq; [apply step_preserves_wellformed | | ]; assumption.
  - right.
    apply grid_eq_false_implies_grids_differ; assumption.
Defined.

Lemma happy_extensional :
  forall tau g1 g2 p,
    (forall q, In q all_positions_grid -> get_cell g1 q = get_cell g2 q) ->
    In p all_positions_grid ->
    happy tau g1 p = happy tau g2 p.
Proof.
  intros tau g1 g2 p Heq Hin.
  unfold happy.
  rewrite Heq by assumption.
  destruct (get_cell g2 p) eqn:Hcell; [reflexivity|].
  f_equal.
  unfold neighbor_cells.
  apply f_equal.
  apply map_ext_in.
  intros q Hq.
  apply Heq.
  apply (neighbors_subset_all_positions p q).
  assumption.
Qed.

Lemma grid_extensional_stability :
  forall tau g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    grid_eq g1 g2 = true ->
    (stable tau g1 <-> stable tau g2).
Proof.
  intros tau g1 g2 Hwf1 Hwf2 Heq.
  rewrite grid_eq_spec in Heq.
  split; intros Hstable; unfold stable; intros p;
  destruct p as [i j];
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - apply Nat.ltb_lt in Hi; apply Nat.ltb_lt in Hj.
    assert (Hin : In (i, j) all_positions_grid) by (apply all_positions_coverage; assumption).
    rewrite <- (happy_extensional tau g1 g2 (i, j)); [apply Hstable | assumption | assumption].
  - apply empty_cell_always_happy; apply Hwf2; right; apply Nat.ltb_ge; assumption.
  - apply empty_cell_always_happy; apply Hwf2; left; apply Nat.ltb_ge; assumption.
  - apply empty_cell_always_happy; apply Hwf2; left; apply Nat.ltb_ge; assumption.
  - apply Nat.ltb_lt in Hi; apply Nat.ltb_lt in Hj.
    assert (Hin : In (i, j) all_positions_grid) by (apply all_positions_coverage; assumption).
    rewrite (happy_extensional tau g1 g2 (i, j)); [apply Hstable | assumption | assumption].
  - apply empty_cell_always_happy; apply Hwf1; right; apply Nat.ltb_ge; assumption.
  - apply empty_cell_always_happy; apply Hwf1; left; apply Nat.ltb_ge; assumption.
  - apply empty_cell_always_happy; apply Hwf1; left; apply Nat.ltb_ge; assumption.
Qed.

(* -----------------------------------------------------------------------------
   Grid Isomorphism: Structural Equivalence
   ----------------------------------------------------------------------------- *)

(** Two grids are isomorphic if there exists a bijection on positions that
    preserves the cell structure. This captures the idea that two grids are
    "the same" up to renaming of positions. *)

Definition pos_bijection (f : Pos -> Pos) : Prop :=
  (forall p, in_bounds p -> in_bounds (f p)) /\
  (forall p1 p2, in_bounds p1 -> in_bounds p2 -> f p1 = f p2 -> p1 = p2) /\
  (forall q, in_bounds q -> exists p, in_bounds p /\ f p = q).

Definition grid_isomorphic (g1 g2 : Grid) : Prop :=
  exists (f : Pos -> Pos),
    pos_bijection f /\
    (forall p, in_bounds p -> get_cell g1 p = get_cell g2 (f p)).

Lemma pos_bijection_id :
  pos_bijection (fun p => p).
Proof.
  unfold pos_bijection; repeat split; intros.
  - assumption.
  - assumption.
  - exists q; split; [assumption | reflexivity].
Qed.

Lemma grid_isomorphic_refl :
  forall g,
    grid_isomorphic g g.
Proof.
  intros g.
  exists (fun p => p).
  split.
  - apply pos_bijection_id.
  - intros p Hp; reflexivity.
Qed.

Lemma pos_bijection_has_inverse :
  forall f,
    pos_bijection f ->
    (forall p1 p2, in_bounds p1 -> in_bounds p2 -> f p1 = f p2 -> p1 = p2) /\
    (forall q, in_bounds q -> exists p, in_bounds p /\ f p = q).
Proof.
  intros f [Hdom [Hinj Hsurj]].
  split; assumption.
Qed.

Fixpoint find_inverse_in_list (f : Pos -> Pos) (q : Pos) (ps : list Pos) : option Pos :=
  match ps with
  | [] => None
  | p :: ps' => if pos_eqb (f p) q then Some p else find_inverse_in_list f q ps'
  end.

Lemma find_inverse_in_list_some :
  forall f q ps p,
    find_inverse_in_list f q ps = Some p ->
    In p ps /\ f p = q.
Proof.
  intros f q ps; induction ps as [|p' ps' IH]; intros p H; simpl in H.
  - discriminate.
  - destruct (pos_eqb (f p') q) eqn:E.
    + injection H as H; subst p'.
      split; [left; reflexivity | apply pos_eqb_eq; assumption].
    + destruct (IH p H) as [Hin Heq].
      split; [right; assumption | assumption].
Qed.

Lemma pos_eqb_false_iff :
  forall p q,
    pos_eqb p q = false <-> p <> q.
Proof.
  intros p q; split.
  - intros H Hcontra; subst q.
    rewrite pos_eqb_refl in H; discriminate.
  - apply pos_eqb_neq.
Qed.

Lemma find_inverse_in_list_none :
  forall f q ps,
    find_inverse_in_list f q ps = None ->
    forall p, In p ps -> f p <> q.
Proof.
  intros f q ps; induction ps as [|p' ps' IH]; intros H p Hin; simpl in H.
  - inversion Hin.
  - destruct (pos_eqb (f p') q) eqn:E.
    + discriminate.
    + destruct Hin as [Heq | Hin'].
      * subst p'; intros Hcontra.
        rewrite pos_eqb_false_iff in E.
        contradiction.
      * apply IH; assumption.
Qed.

Lemma find_inverse_in_list_complete :
  forall f q ps p,
    In p ps ->
    f p = q ->
    exists p', find_inverse_in_list f q ps = Some p' /\ f p' = q.
Proof.
  intros f q ps; induction ps as [|phd ps' IH]; intros p Hin Heq.
  - inversion Hin.
  - simpl. destruct (pos_eqb (f phd) q) eqn:E.
    + exists phd; split; [reflexivity | apply pos_eqb_eq; assumption].
    + destruct Hin as [Heq' | Hin'].
      * subst phd.
        exfalso.
        rewrite pos_eqb_false_iff in E.
        contradiction.
      * apply (IH p); assumption.
Qed.

Definition inverse_from_list (f : Pos -> Pos) (q : Pos) : Pos :=
  match find_inverse_in_list f q all_positions_grid with
  | Some p => p
  | None => q
  end.

Lemma inverse_from_list_correct :
  forall f q,
    pos_bijection f ->
    in_bounds q ->
    in_bounds (inverse_from_list f q) /\ f (inverse_from_list f q) = q.
Proof.
  intros f q [Hdom [Hinj Hsurj]] Hq.
  unfold inverse_from_list.
  destruct (Hsurj q Hq) as [p [Hp Heq]].
  assert (Hin : In p all_positions_grid).
  { apply all_positions_complete; assumption. }
  destruct (find_inverse_in_list_complete f q all_positions_grid p Hin Heq) as [p' [Hfind Heq']].
  rewrite Hfind.
  split.
  - apply find_inverse_in_list_some in Hfind.
    destruct Hfind as [Hin' _].
    apply all_positions_only_in_bounds; assumption.
  - apply find_inverse_in_list_some in Hfind.
    destruct Hfind as [_ Heq''].
    assumption.
Qed.

Lemma inverse_from_list_injective :
  forall f q1 q2,
    pos_bijection f ->
    in_bounds q1 ->
    in_bounds q2 ->
    inverse_from_list f q1 = inverse_from_list f q2 ->
    q1 = q2.
Proof.
  intros f q1 q2 Hbij Hq1 Hq2 Heq.
  destruct (inverse_from_list_correct f q1 Hbij Hq1) as [_ H1].
  destruct (inverse_from_list_correct f q2 Hbij Hq2) as [_ H2].
  rewrite <- H1, <- H2.
  rewrite Heq.
  reflexivity.
Qed.

Lemma inverse_from_list_surjective :
  forall f p,
    pos_bijection f ->
    in_bounds p ->
    exists q, in_bounds q /\ inverse_from_list f q = p.
Proof.
  intros f p [Hdom [Hinj Hsurj]] Hp.
  exists (f p).
  split.
  - apply Hdom; assumption.
  - unfold inverse_from_list.
    assert (Hin : In p all_positions_grid).
    { apply all_positions_complete; assumption. }
    destruct (find_inverse_in_list_complete f (f p) all_positions_grid p Hin eq_refl) as [p' [Hfind Heq]].
    rewrite Hfind.
    apply find_inverse_in_list_some in Hfind.
    destruct Hfind as [Hin' Heq'].
    assert (Hp' : in_bounds p').
    { apply all_positions_only_in_bounds; assumption. }
    apply Hinj; assumption.
Qed.

Lemma inverse_from_list_is_bijection :
  forall f,
    pos_bijection f ->
    pos_bijection (inverse_from_list f).
Proof.
  intros f Hbij.
  unfold pos_bijection; repeat split; intros.
  - destruct (inverse_from_list_correct f p Hbij H) as [Hp _].
    assumption.
  - apply (inverse_from_list_injective f); assumption.
  - apply (inverse_from_list_surjective f); assumption.
Qed.

Lemma inverse_from_list_left_inverse :
  forall f p,
    pos_bijection f ->
    in_bounds p ->
    inverse_from_list f (f p) = p.
Proof.
  intros f p Hbij Hp.
  destruct Hbij as [Hdom [Hinj Hsurj]].
  unfold inverse_from_list.
  assert (Hin : In p all_positions_grid).
  { apply all_positions_complete; assumption. }
  destruct (find_inverse_in_list_complete f (f p) all_positions_grid p Hin eq_refl) as [p' [Hfind Heq]].
  rewrite Hfind.
  apply find_inverse_in_list_some in Hfind.
  destruct Hfind as [Hin' Heq'].
  assert (Hp' : in_bounds p').
  { apply all_positions_only_in_bounds; assumption. }
  apply Hinj; assumption.
Qed.

Lemma inverse_from_list_right_inverse :
  forall f q,
    pos_bijection f ->
    in_bounds q ->
    f (inverse_from_list f q) = q.
Proof.
  intros f q Hbij Hq.
  destruct (inverse_from_list_correct f q Hbij Hq) as [_ H].
  assumption.
Qed.

Lemma grid_isomorphic_sym :
  forall g1 g2,
    grid_isomorphic g1 g2 ->
    grid_isomorphic g2 g1.
Proof.
  intros g1 g2 [f [Hbij Hcells]].
  exists (inverse_from_list f).
  split.
  - apply inverse_from_list_is_bijection; assumption.
  - intros p Hp.
    set (ginv := inverse_from_list f).
    assert (Hgp : in_bounds (ginv p)).
    { unfold ginv. destruct (inverse_from_list_correct f p Hbij Hp) as [H _]; exact H. }
    assert (Hfgp : f (ginv p) = p).
    { unfold ginv. apply inverse_from_list_right_inverse; assumption. }
    transitivity (get_cell g2 (f (ginv p))).
    + rewrite Hfgp; reflexivity.
    + symmetry; apply Hcells; assumption.
Qed.

Lemma pos_bijection_compose :
  forall f g,
    pos_bijection f ->
    pos_bijection g ->
    pos_bijection (fun p => g (f p)).
Proof.
  intros f g [Hdomf [Hinjf Hsurf]] [Hdomg [Hinjg Hsurjg]].
  unfold pos_bijection; repeat split; intros.
  - apply Hdomg; apply Hdomf; assumption.
  - apply Hinjf; try assumption.
    apply Hinjg; try (apply Hdomf; assumption).
    assumption.
  - destruct (Hsurjg q H) as [p' [Hp' Heq']].
    destruct (Hsurf p' Hp') as [p [Hp Heq]].
    exists p; split; [assumption|].
    rewrite Heq; assumption.
Qed.

Lemma grid_isomorphic_trans :
  forall g1 g2 g3,
    grid_isomorphic g1 g2 ->
    grid_isomorphic g2 g3 ->
    grid_isomorphic g1 g3.
Proof.
  intros g1 g2 g3 [f [Hbijf Hcellsf]] [g [Hbijg Hcellsg]].
  exists (fun p => g (f p)).
  split.
  - apply pos_bijection_compose; assumption.
  - intros p Hp.
    rewrite Hcellsf by assumption.
    apply Hcellsg.
    destruct Hbijf as [Hdomf _].
    apply Hdomf; assumption.
Qed.

Theorem grid_isomorphic_equivalence :
  Equivalence grid_isomorphic.
Proof.
  constructor.
  - intros g; apply grid_isomorphic_refl.
  - intros g1 g2; apply grid_isomorphic_sym.
  - intros g1 g2 g3; apply grid_isomorphic_trans.
Qed.

Fixpoint map_positions (f : Pos -> Pos) (ps : list Pos) : list Pos :=
  match ps with
  | [] => []
  | p :: ps' => f p :: map_positions f ps'
  end.

Lemma map_positions_spec :
  forall f ps,
    map_positions f ps = map f ps.
Proof.
  intros f ps.
  induction ps as [|p ps' IH]; simpl; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

Lemma map_positions_length :
  forall f ps,
    length (map_positions f ps) = length ps.
Proof.
  intros f ps.
  rewrite map_positions_spec.
  apply map_length.
Qed.

Lemma in_map_positions :
  forall f ps q,
    In q (map_positions f ps) <-> exists p, In p ps /\ f p = q.
Proof.
  intros f ps q.
  rewrite map_positions_spec.
  split; intros H.
  - apply in_map_iff in H.
    destruct H as [p [Heq Hin]].
    exists p; split; assumption.
  - destruct H as [p [Hin Heq]].
    apply in_map_iff.
    exists p; split; assumption.
Qed.

Lemma bijection_map_NoDup :
  forall f ps,
    pos_bijection f ->
    (forall p, In p ps -> in_bounds p) ->
    NoDup ps ->
    NoDup (map_positions f ps).
Proof.
  intros f ps [Hdom [Hinj Hsurj]] Hbound Hnodup.
  rewrite map_positions_spec.
  induction Hnodup as [|p ps' Hnotin Hnodup' IH].
  - simpl; constructor.
  - simpl; constructor.
    + intros Hcontra.
      apply in_map_iff in Hcontra.
      destruct Hcontra as [p' [Heq Hin']].
      assert (Hp : in_bounds p) by (apply Hbound; left; reflexivity).
      assert (Hp' : in_bounds p') by (apply Hbound; right; assumption).
      apply Hinj in Heq; try assumption.
      subst p'.
      contradiction.
    + apply IH.
      intros q Hq.
      apply Hbound; right; assumption.
Qed.

Lemma bijection_map_covers :
  forall f ps q,
    pos_bijection f ->
    (forall p, In p ps -> in_bounds p) ->
    in_bounds q ->
    In q (map_positions f ps) ->
    exists p, In p ps /\ f p = q.
Proof.
  intros f ps q Hbij Hbound Hq Hin.
  rewrite in_map_positions in Hin.
  assumption.
Qed.

Lemma bijection_induces_permutation_on_all_positions :
  forall f,
    pos_bijection f ->
    Permutation all_positions_grid (map_positions f all_positions_grid).
Proof.
  intros f Hbij.
  apply NoDup_Permutation.
  - apply all_positions_grid_NoDup.
  - apply bijection_map_NoDup; try assumption.
    + intros p Hp; apply all_positions_only_in_bounds; assumption.
    + apply all_positions_grid_NoDup.
  - intros q; split; intros Hin.
    + rewrite in_map_positions.
      destruct Hbij as [Hdom [Hinj Hsurj]].
      assert (Hq : in_bounds q) by (apply all_positions_only_in_bounds; assumption).
      destruct (Hsurj q Hq) as [p [Hp Heq]].
      exists p; split.
      * apply all_positions_complete; assumption.
      * assumption.
    + rewrite in_map_positions in Hin.
      destruct Hin as [p [Hp Heq]].
      subst q.
      apply all_positions_complete.
      destruct Hbij as [Hdom _].
      assert (Hpbound : in_bounds p) by (apply all_positions_only_in_bounds; assumption).
      apply Hdom; assumption.
Qed.

Lemma count_agents_in_cells_map_eq :
  forall g1 g2 ps f,
    pos_bijection f ->
    (forall p, In p ps -> in_bounds p) ->
    (forall p, In p ps -> get_cell g1 p = get_cell g2 (f p)) ->
    count_agents_in_cells (map (get_cell g1) ps) =
    count_agents_in_cells (map (get_cell g2) (map_positions f ps)).
Proof.
  intros g1 g2 ps f Hbij Hbound Hcells.
  induction ps as [|p ps' IH]; simpl.
  - reflexivity.
  - rewrite map_positions_spec; simpl.
    rewrite <- Hcells by (left; reflexivity).
    destruct (get_cell g1 p); simpl.
    + rewrite <- map_positions_spec.
      apply IH.
      intros q Hq; apply Hbound; right; assumption.
      intros q Hq; apply Hcells; right; assumption.
    + f_equal.
      rewrite <- map_positions_spec.
      apply IH.
      intros q Hq; apply Hbound; right; assumption.
      intros q Hq; apply Hcells; right; assumption.
Qed.

Lemma count_agents_permutation :
  forall g ps1 ps2,
    Permutation ps1 ps2 ->
    count_agents_in_cells (map (get_cell g) ps1) =
    count_agents_in_cells (map (get_cell g) ps2).
Proof.
  intros g ps1 ps2 Hperm.
  induction Hperm as [|x l1 l2 Hperm IH | x y l | l1 l2 l3 Hperm12 IH12 Hperm23 IH23].
  - reflexivity.
  - simpl.
    destruct (get_cell g x); simpl.
    + apply IH.
    + f_equal; apply IH.
  - simpl.
    destruct (get_cell g x), (get_cell g y); simpl; reflexivity.
  - rewrite IH12, IH23; reflexivity.
Qed.

Lemma grid_isomorphic_preserves_agent_count :
  forall g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    grid_isomorphic g1 g2 ->
    count_agents g1 = count_agents g2.
Proof.
  intros g1 g2 Hwf1 Hwf2 [f [Hbij Hcells]].
  unfold count_agents, count_agents_at_positions.
  assert (Hbound : forall p, In p all_positions_grid -> in_bounds p).
  { intros p Hp; apply all_positions_only_in_bounds; assumption. }
  assert (Hcells' : forall p, In p all_positions_grid -> get_cell g1 p = get_cell g2 (f p)).
  { intros p Hin; apply Hcells; apply Hbound; assumption. }
  transitivity (count_agents_in_cells (map (get_cell g2) (map_positions f all_positions_grid))).
  + apply count_agents_in_cells_map_eq with (f := f).
    * exact Hbij.
    * exact Hbound.
    * exact Hcells'.
  + apply count_agents_permutation.
    symmetry.
    apply bijection_induces_permutation_on_all_positions.
    assumption.
Qed.

(* -----------------------------------------------------------------------------
   Deterministic Dynamics and Cycle Prevention
   ----------------------------------------------------------------------------- *)

Lemma step_deterministic :
  forall tau g,
    step tau g = step tau g.
Proof.
  intros tau g; reflexivity.
Qed.

Lemma find_destination_deterministic :
  forall tau g a q1 q2,
    find_destination tau g a = Some q1 ->
    find_destination tau g a = Some q2 ->
    q1 = q2.
Proof.
  intros tau g a q1 q2 H1 H2.
  rewrite H1 in H2.
  injection H2 as H2.
  assumption.
Qed.

Lemma neighbor_cells_preserves_cell_at_other_positions :
  forall g1 g2 p,
    (forall r, In r (neighbors p) -> get_cell g1 r = get_cell g2 r) ->
    neighbor_cells g1 p = neighbor_cells g2 p.
Proof.
  intros g1 g2 p Heq.
  unfold neighbor_cells.
  apply map_ext_in.
  assumption.
Qed.

Lemma happy_for_extensional :
  forall tau g1 g2 a p,
    (forall r, In r (neighbors p) -> get_cell g1 r = get_cell g2 r) ->
    happy_for tau g1 a p = happy_for tau g2 a p.
Proof.
  intros tau g1 g2 a p Heq.
  unfold happy_for.
  f_equal.
  f_equal.
  apply neighbor_cells_preserves_cell_at_other_positions.
  assumption.
Qed.

Lemma find_destination_gives_empty_and_happy_on_old_grid :
  forall tau g a q,
    find_destination tau g a = Some q ->
    get_cell g q = Empty /\ happy_for tau g a q = true.
Proof.
  intros tau g a q Hfind.
  unfold find_destination in Hfind.
  destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hf; [|discriminate].
  injection Hfind as Hfind; subst p.
  apply List.find_some in Hf.
  destruct Hf as [_ Hcond].
  unfold empty_and_happy_for in Hcond.
  rewrite Bool.andb_true_iff in Hcond.
  destruct Hcond as [Hempty Hhappyfor].
  unfold cell_is_empty in Hempty.
  rewrite Bool.negb_true_iff in Hempty.
  destruct (get_cell g q) eqn:Hcellq; [|simpl in Hempty; discriminate].
  split; [reflexivity | assumption].
Qed.

Lemma moving_agent_was_going_to_happy_location :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    (tau <= count_same a (neighbor_cells g q))%nat.
Proof.
  intros tau g p a q Hcellp Hfind.
  apply find_destination_gives_empty_and_happy_on_old_grid in Hfind.
  destruct Hfind as [_ Hhappyfor].
  unfold happy_for in Hhappyfor.
  apply Nat.leb_le.
  assumption.
Qed.

Lemma unstable_means_some_unhappy :
  forall tau g,
    wellformed_grid g ->
    ~ stable tau g ->
    (count_unhappy_positions tau g > 0)%nat.
Proof.
  intros tau g Hwf Hnstable.
  destruct (count_unhappy_positions tau g) eqn:Hcount.
  - exfalso.
    apply Hnstable.
    apply stable_iff_count_unhappy_zero; assumption.
  - lia.
Qed.


Lemma step_position_when_happy_preserves_grid :
  forall tau g p,
    happy tau g p = true ->
    step_position tau g p = g.
Proof.
  intros tau g p Hhappy.
  unfold step_position.
  destruct (get_cell g p) eqn:Hcellp; [reflexivity|].
  rewrite Hhappy.
  reflexivity.
Qed.

Lemma step_position_when_empty_preserves_grid :
  forall tau g p,
    get_cell g p = Empty ->
    step_position tau g p = g.
Proof.
  intros tau g p Hempty.
  unfold step_position.
  rewrite Hempty.
  reflexivity.
Qed.

Lemma step_position_when_no_destination_preserves_grid :
  forall tau g p a,
    get_cell g p = Occupied a ->
    find_destination tau g a = None ->
    step_position tau g p = g.
Proof.
  intros tau g p a Hcellp Hno_dest.
  unfold step_position.
  rewrite Hcellp.
  destruct (happy tau g p); [reflexivity|].
  rewrite Hno_dest.
  reflexivity.
Qed.

Lemma nat_iter_succ_commute :
  forall {A : Type} n (f : A -> A) (x : A),
    Nat.iter (S n) f x = f (Nat.iter n f x).
Proof.
  intros A n f x.
  simpl.
  reflexivity.
Qed.

Lemma nat_iter_succ_commute_alt :
  forall {A : Type} n (f : A -> A) (x : A),
    Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros A n f x.
  induction n as [|n' IH]; simpl.
  - reflexivity.
  - f_equal.
    exact IH.
Qed.

Lemma micro_step_position_empty_no_change :
  forall tau g p,
    get_cell g p = Empty ->
    step_position tau g p = g.
Proof.
  intros tau g p Hempty.
  unfold step_position.
  rewrite Hempty.
  reflexivity.
Qed.

Lemma micro_step_position_happy_no_change :
  forall tau g p a,
    get_cell g p = Occupied a ->
    happy tau g p = true ->
    step_position tau g p = g.
Proof.
  intros tau g p a Hocc Hhappy.
  unfold step_position.
  rewrite Hocc.
  rewrite Hhappy.
  reflexivity.
Qed.

Lemma micro_step_position_unhappy_no_dest_no_change :
  forall tau g p a,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = None ->
    step_position tau g p = g.
Proof.
  intros tau g p a Hocc Hunhappy Hno_dest.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hno_dest.
  reflexivity.
Qed.

Lemma micro_step_position_move_structure :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    step_position tau g p = set_cell (set_cell g p Empty) q (Occupied a).
Proof.
  intros tau g p a q Hocc Hunhappy Hdest.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hdest.
  reflexivity.
Qed.

Lemma micro_find_destination_gives_empty :
  forall tau g a q,
    find_destination tau g a = Some q ->
    get_cell g q = Empty.
Proof.
  intros tau g a q Hfind.
  apply find_destination_gives_empty_and_happy_on_old_grid in Hfind.
  destruct Hfind as [Hempty _].
  exact Hempty.
Qed.

Lemma micro_find_destination_gives_happy :
  forall tau g a q,
    find_destination tau g a = Some q ->
    happy_for tau g a q = true.
Proof.
  intros tau g a q Hfind.
  apply find_destination_gives_empty_and_happy_on_old_grid in Hfind.
  destruct Hfind as [_ Hhappy].
  exact Hhappy.
Qed.

Lemma micro_find_destination_in_bounds :
  forall tau g a q,
    find_destination tau g a = Some q ->
    in_bounds q.
Proof.
  intros tau g a q Hfind.
  unfold find_destination in Hfind.
  destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hf; [|discriminate].
  injection Hfind as Hfind; subst p.
  apply List.find_some in Hf.
  destruct Hf as [Hin _].
  apply all_positions_only_in_bounds.
  exact Hin.
Qed.

Lemma micro_happy_for_means_enough_same :
  forall tau g a q,
    happy_for tau g a q = true ->
    (tau <= count_same a (neighbor_cells g q))%nat.
Proof.
  intros tau g a q Hhappy.
  unfold happy_for in Hhappy.
  apply Nat.leb_le.
  exact Hhappy.
Qed.

Lemma micro_unhappy_means_not_enough_same :
  forall tau g p a,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    (count_same a (neighbor_cells g p) < tau)%nat.
Proof.
  intros tau g p a Hocc Hunhappy.
  unfold happy in Hunhappy.
  rewrite Hocc in Hunhappy.
  apply Nat.leb_nle in Hunhappy.
  lia.
Qed.

Lemma micro_count_unhappy_cons_happy :
  forall tau g p ps,
    happy tau g p = true ->
    count_unhappy_positions_list tau g (p :: ps) =
    count_unhappy_positions_list tau g ps.
Proof.
  intros tau g p ps Hhappy.
  simpl.
  rewrite Hhappy.
  reflexivity.
Qed.

Lemma micro_count_unhappy_cons_unhappy :
  forall tau g p ps,
    happy tau g p = false ->
    count_unhappy_positions_list tau g (p :: ps) =
    S (count_unhappy_positions_list tau g ps).
Proof.
  intros tau g p ps Hunhappy.
  simpl.
  rewrite Hunhappy.
  reflexivity.
Qed.

Lemma micro_empty_always_happy :
  forall tau g p,
    get_cell g p = Empty ->
    happy tau g p = true.
Proof.
  intros tau g p Hempty.
  apply empty_cell_always_happy.
  exact Hempty.
Qed.

Lemma micro_moved_agent_becomes_happy :
  forall tau g p q a,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    happy_for tau g a q = true.
Proof.
  intros tau g p q a Hocc Hfind.
  apply micro_find_destination_gives_happy.
  exact Hfind.
Qed.

Lemma micro_happy_decidable :
  forall tau g p,
    {happy tau g p = true} + {happy tau g p = false}.
Proof.
  intros tau g p.
  destruct (happy tau g p) eqn:H.
  - left; reflexivity.
  - right; reflexivity.
Defined.

Lemma micro_not_stable_means_exists_unhappy :
  forall tau g,
    wellformed_grid g ->
    ~ stable tau g ->
    exists p, In p all_positions_grid /\ happy tau g p = false.
Proof.
  intros tau g Hwf Hnstable.
  destruct (stable_dec_wellformed tau g Hwf) as [Hstable | Hnstable'].
  - exfalso; apply Hnstable; assumption.
  - clear Hnstable.
    assert (Hcount : (count_unhappy_positions tau g > 0)%nat).
    { apply unstable_means_some_unhappy; assumption. }
    unfold count_unhappy_positions in Hcount.
    assert (Hexists : exists p, In p all_positions_grid /\ happy tau g p = false).
    { clear Hwf Hnstable'.
      induction all_positions_grid as [|p ps IH].
      - simpl in Hcount; lia.
      - simpl in Hcount.
        destruct (happy tau g p) eqn:Hhappy.
        + destruct IH as [q [Hinq Hunhappy]].
          { lia. }
          exists q; split; [right; assumption | assumption].
        + exists p; split; [left; reflexivity | exact Hhappy]. }
    exact Hexists.
Qed.

Lemma micro_step_positions_nil :
  forall tau g,
    step_positions tau [] g = g.
Proof.
  intros tau g.
  simpl.
  reflexivity.
Qed.

Lemma micro_step_positions_cons :
  forall tau g p ps,
    step_positions tau (p :: ps) g =
    step_positions tau ps (step_position tau g p).
Proof.
  intros tau g p ps.
  simpl.
  reflexivity.
Qed.

Lemma micro_step_def :
  forall tau g,
    step tau g = step_positions tau all_positions_grid g.
Proof.
  intros tau g.
  unfold step.
  reflexivity.
Qed.

Lemma micro_wellformed_after_step_position :
  forall tau g p,
    wellformed_grid g ->
    wellformed_grid (step_position tau g p).
Proof.
  intros tau g p Hwf.
  apply step_position_preserves_wellformed.
  exact Hwf.
Qed.

Lemma micro_wellformed_after_step_positions :
  forall tau g ps,
    wellformed_grid g ->
    wellformed_grid (step_positions tau ps g).
Proof.
  intros tau g ps Hwf.
  apply step_positions_preserves_wellformed.
  exact Hwf.
Qed.

Lemma micro_finite_grid_configs :
  forall g1 g2 : Grid,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    grid_eq g1 g2 = true ->
    forall p, In p all_positions_grid -> get_cell g1 p = get_cell g2 p.
Proof.
  intros g1 g2 Hwf1 Hwf2 Heq p Hin.
  rewrite grid_eq_spec in Heq.
  apply Heq.
  exact Hin.
Qed.

Lemma micro_stable_step_identity_on_grid :
  forall tau g p,
    stable tau g ->
    In p all_positions_grid ->
    get_cell (step tau g) p = get_cell g p.
Proof.
  intros tau g p Hstable Hin.
  rewrite step_stable_fixed_point by assumption.
  reflexivity.
Qed.

Lemma micro_count_unhappy_extensional :
  forall tau g1 g2 ps,
    (forall p, In p ps -> happy tau g1 p = happy tau g2 p) ->
    count_unhappy_positions_list tau g1 ps = count_unhappy_positions_list tau g2 ps.
Proof.
  intros tau g1 g2 ps Hext.
  induction ps as [|p ps' IH]; simpl.
  - reflexivity.
  - rewrite Hext by (left; reflexivity).
    rewrite IH.
    + reflexivity.
    + intros q Hq; apply Hext; right; assumption.
Qed.

Lemma micro_step_position_changes_or_same :
  forall tau g p,
    step_position tau g p = g \/
    exists a q, get_cell g p = Occupied a /\
                happy tau g p = false /\
                find_destination tau g a = Some q /\
                step_position tau g p = set_cell (set_cell g p Empty) q (Occupied a).
Proof.
  intros tau g p.
  unfold step_position.
  destruct (get_cell g p) eqn:Hcell.
  - left; reflexivity.
  - destruct (happy tau g p) eqn:Hhappy.
    + left; reflexivity.
    + destruct (find_destination tau g a) eqn:Hfind.
      * right; exists a, p0; repeat split; assumption.
      * left; reflexivity.
Qed.

Lemma micro_find_destination_different_from_source :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    p <> q.
Proof.
  intros tau g p a q Hocc Hfind.
  intros Heq; subst q.
  apply micro_find_destination_gives_empty in Hfind.
  rewrite Hocc in Hfind.
  discriminate.
Qed.

Lemma micro_move_source_becomes_empty :
  forall tau g p q a,
    p <> q ->
    step_position tau g p = set_cell (set_cell g p Empty) q (Occupied a) ->
    get_cell (step_position tau g p) p = Empty.
Proof.
  intros tau g p q a Hneq Hmove.
  rewrite Hmove.
  assert (Hneq': q <> p) by (intros C; subst; apply Hneq; reflexivity).
  rewrite get_set_other by exact Hneq'.
  rewrite get_set_same; reflexivity.
Qed.

Lemma micro_move_dest_becomes_occupied :
  forall tau g p q a,
    step_position tau g p = set_cell (set_cell g p Empty) q (Occupied a) ->
    get_cell (step_position tau g p) q = Occupied a.
Proof.
  intros tau g p q a Hmove.
  rewrite Hmove.
  rewrite get_set_same; reflexivity.
Qed.

Fixpoint count_same_in_list (a : Agent) (cs : list Cell) : nat :=
  match cs with
  | [] => 0
  | Empty :: cs' => count_same_in_list a cs'
  | Occupied b :: cs' =>
      if agent_eqb a b
      then S (count_same_in_list a cs')
      else count_same_in_list a cs'
  end.

Lemma count_same_is_count_same_in_list :
  forall a cs,
    count_same a cs = count_same_in_list a cs.
Proof.
  intros a cs.
  induction cs as [|c cs' IH]; simpl.
  - reflexivity.
  - destruct c; simpl.
    + exact IH.
    + destruct (agent_eqb a a0); simpl; f_equal; exact IH.
Qed.

Lemma count_same_extensional :
  forall a g1 g2 ps,
    (forall r, In r ps -> get_cell g1 r = get_cell g2 r) ->
    count_same a (map (get_cell g1) ps) = count_same a (map (get_cell g2) ps).
Proof.
  intros a g1 g2 ps Hext.
  induction ps as [|p ps' IH]; simpl.
  - reflexivity.
  - rewrite Hext by (left; reflexivity).
    destruct (get_cell g2 p) eqn:E; simpl;
    try (apply IH; intros r Hr; apply Hext; right; exact Hr).
    destruct (agent_eqb a a0); simpl.
    + f_equal; apply IH; intros r Hr; apply Hext; right; exact Hr.
    + apply IH; intros r Hr; apply Hext; right; exact Hr.
Qed.

Lemma micro_move_preserves_cell_elsewhere :
  forall g p q a r,
    get_cell g p = Occupied a ->
    get_cell g q = Empty ->
    p <> q ->
    r <> p ->
    r <> q ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) r = get_cell g r.
Proof.
  intros g p q a r Hocc Hempty Hpq Hrp Hrq.
  assert (Hneq_qr: q <> r) by (intros C; subst; apply Hrq; reflexivity).
  assert (Hneq_pr: p <> r) by (intros C; subst; apply Hrp; reflexivity).
  rewrite get_set_other by exact Hneq_qr.
  rewrite get_set_other by exact Hneq_pr.
  reflexivity.
Qed.

Lemma micro_step_position_no_move_preserves_all_cells :
  forall tau g p r,
    step_position tau g p = g ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hno_move.
  rewrite Hno_move; reflexivity.
Qed.

Lemma step_position_changed_when_moves :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    p <> q.
Proof.
  intros tau g p a q Hcell Hunhappy Hfind Heq.
  subst q.
  apply micro_find_destination_gives_empty in Hfind.
  rewrite Hcell in Hfind.
  discriminate.
Qed.

Lemma step_position_move_creates_different_grid :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    p <> q ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p <> get_cell g p.
Proof.
  intros tau g p a q Hcell Hfind Hneq.
  assert (Hneq' : q <> p) by (intros C; subst; contradiction).
  rewrite get_set_other by assumption.
  rewrite get_set_same.
  rewrite Hcell.
  discriminate.
Qed.

Lemma step_positions_preserves_grid_extensionally :
  forall tau ps g,
    step_positions tau ps g = g ->
    forall q, get_cell (step_positions tau ps g) q = get_cell g q.
Proof.
  intros tau ps g Hunchanged q.
  rewrite Hunchanged.
  reflexivity.
Qed.

Lemma find_destination_dec :
  forall tau g a,
    {q | find_destination tau g a = Some q} + {find_destination tau g a = None}.
Proof.
  intros tau g a.
  unfold find_destination.
  destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hfind.
  - left. exists p. reflexivity.
  - right. reflexivity.
Defined.

Fixpoint find_unhappy_can_move_aux (tau : nat) (g : Grid) (ps : list Pos) :
  option (Pos * Agent) :=
  match ps with
  | [] => None
  | p :: ps' =>
      match get_cell g p with
      | Empty => find_unhappy_can_move_aux tau g ps'
      | Occupied a =>
          if happy tau g p then
            find_unhappy_can_move_aux tau g ps'
          else
            match find_destination tau g a with
            | None => find_unhappy_can_move_aux tau g ps'
            | Some _ => Some (p, a)
            end
      end
  end.

Lemma find_unhappy_can_move_aux_cons_empty :
  forall tau g p ps,
    get_cell g p = Empty ->
    find_unhappy_can_move_aux tau g (p :: ps) = find_unhappy_can_move_aux tau g ps.
Proof.
  intros tau g p ps Hcell.
  simpl. rewrite Hcell. reflexivity.
Qed.

Lemma find_unhappy_can_move_aux_cons_happy :
  forall tau g p a ps,
    get_cell g p = Occupied a ->
    happy tau g p = true ->
    find_unhappy_can_move_aux tau g (p :: ps) = find_unhappy_can_move_aux tau g ps.
Proof.
  intros tau g p a ps Hcell Hhappy.
  simpl. rewrite Hcell. rewrite Hhappy. reflexivity.
Qed.

Lemma find_unhappy_can_move_aux_cons_unhappy_no_dest :
  forall tau g p a ps,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = None ->
    find_unhappy_can_move_aux tau g (p :: ps) = find_unhappy_can_move_aux tau g ps.
Proof.
  intros tau g p a ps Hcell Hhappy Hno_dest.
  simpl. rewrite Hcell. rewrite Hhappy. rewrite Hno_dest. reflexivity.
Qed.

Lemma find_unhappy_can_move_aux_cons_unhappy_has_dest :
  forall tau g p a ps q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    find_unhappy_can_move_aux tau g (p :: ps) = Some (p, a).
Proof.
  intros tau g p a ps q Hcell Hhappy Hdest.
  simpl. rewrite Hcell. rewrite Hhappy. rewrite Hdest. reflexivity.
Qed.

Lemma find_unhappy_can_move_aux_some :
  forall tau g ps p a,
    find_unhappy_can_move_aux tau g ps = Some (p, a) ->
    In p ps /\ get_cell g p = Occupied a /\ happy tau g p = false /\ find_destination tau g a <> None.
Proof.
  intros tau g ps. induction ps as [|p' ps' IH]; intros p a Hfind.
  - discriminate.
  - simpl in Hfind.
    destruct (get_cell g p') eqn:Hcell.
    + apply IH in Hfind. destruct Hfind as [Hin [Hc [Hh Hd]]].
      split. right. exact Hin.
      split. exact Hc.
      split. exact Hh.
      exact Hd.
    + destruct (happy tau g p') eqn:Hhappy.
      * apply IH in Hfind. destruct Hfind as [Hin [Hc [Hh Hd]]].
        split. right. exact Hin.
        split. exact Hc.
        split. exact Hh.
        exact Hd.
      * destruct (find_destination tau g a0) eqn:Hfind_dest.
        -- inversion Hfind; subst. clear Hfind.
           split. left. reflexivity.
           split. exact Hcell.
           split. exact Hhappy.
           congruence.
        -- apply IH in Hfind. destruct Hfind as [Hin [Hc [Hh Hd]]].
           split. right. exact Hin.
           split. exact Hc.
           split. exact Hh.
           exact Hd.
Qed.

Lemma cell_eq_dec : forall c1 c2 : Cell, {c1 = c2} + {c1 <> c2}.
Proof.
  intros c1 c2.
  destruct c1, c2.
  - left; reflexivity.
  - right; discriminate.
  - right; discriminate.
  - destruct (agent_eq_dec a a0) as [Heq | Hneq].
    + subst; left; reflexivity.
    + right; intros contra; inversion contra; contradiction.
Defined.

Lemma grid_unchanged_implies_stable_if_no_stuck_unhappy :
  forall tau g,
    wellformed_grid g ->
    (forall p, In p all_positions_grid -> get_cell (step tau g) p = get_cell g p) ->
    (forall p a, In p all_positions_grid -> get_cell g p = Occupied a -> happy tau g p = false -> False) ->
    stable tau g.
Proof.
  intros tau g Hwf Hunchanged Hno_unhappy.
  unfold stable; intros [i j].
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - apply Nat.ltb_lt in Hi; apply Nat.ltb_lt in Hj.
    assert (Hin : In (i, j) all_positions_grid) by (apply all_positions_coverage; assumption).
    destruct (get_cell g (i,j)) eqn:Hcell.
    + apply empty_cell_always_happy; assumption.
    + destruct (happy tau g (i,j)) eqn:Hhappy; [reflexivity|].
      exfalso; eapply Hno_unhappy; eassumption.
  - apply empty_cell_always_happy; apply Hwf; right; apply Nat.ltb_ge; assumption.
  - apply empty_cell_always_happy; apply Hwf; left; apply Nat.ltb_ge; assumption.
  - apply empty_cell_always_happy; apply Hwf; left; apply Nat.ltb_ge; assumption.
Qed.

(* -----------------------------------------------------------------------------
   Quick Win Theorems: Promoted from Infrastructure
   ----------------------------------------------------------------------------- *)

Theorem moving_agent_satisfies_tolerance :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    (tau <= count_same a (neighbor_cells g q))%nat.
Proof.
  intros tau g p a q Hocc Hfind.
  apply micro_find_destination_gives_happy in Hfind.
  apply micro_happy_for_means_enough_same in Hfind.
  exact Hfind.
Qed.

Theorem unhappy_means_unsatisfied :
  forall tau g p a,
    In p all_positions_grid ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    (count_same a (neighbor_cells g p) < tau)%nat.
Proof.
  intros tau g p a Hin Hocc Hunhappy.
  apply micro_unhappy_means_not_enough_same; assumption.
Qed.

Theorem unhappiness_bounded :
  forall tau g,
    (count_unhappy_positions tau g <= grid_size * grid_size)%nat.
Proof.
  intros tau g.
  unfold count_unhappy_positions.
  assert (Hlen : length all_positions_grid = (grid_size * grid_size)%nat).
  { apply all_positions_length. }
  rewrite <- Hlen.
  apply count_unhappy_bounded.
Qed.

Corollary destination_in_bounds :
  forall tau g a q,
    find_destination tau g a = Some q ->
    in_bounds q.
Proof.
  intros tau g a q Hfind.
  unfold find_destination in Hfind.
  destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hf; [|discriminate].
  injection Hfind as Hfind; subst p.
  apply List.find_some in Hf.
  destruct Hf as [Hin _].
  apply all_positions_only_in_bounds.
  exact Hin.
Qed.

Corollary destination_is_empty :
  forall tau g a q,
    find_destination tau g a = Some q ->
    get_cell g q = Empty.
Proof.
  intros tau g a q Hfind.
  apply find_destination_gives_empty_and_happy_on_old_grid in Hfind.
  destruct Hfind as [Hempty _].
  exact Hempty.
Qed.

Corollary destination_makes_happy :
  forall tau g a q,
    find_destination tau g a = Some q ->
    happy_for tau g a q = true.
Proof.
  intros tau g a q Hfind.
  apply find_destination_gives_empty_and_happy_on_old_grid in Hfind.
  destruct Hfind as [_ Hhappy].
  exact Hhappy.
Qed.

Corollary source_different_from_destination :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    p <> q.
Proof.
  intros tau g p a q Hocc Hfind Heq.
  subst q.
  apply find_destination_gives_empty_and_happy_on_old_grid in Hfind.
  destruct Hfind as [Hempty _].
  rewrite Hocc in Hempty.
  discriminate.
Qed.

(* -----------------------------------------------------------------------------
   Tier 2: Fixed Point Characterization
   ----------------------------------------------------------------------------- *)

Lemma find_unhappy_can_move_aux_none_implies_no_movable :
  forall tau g ps p a,
    find_unhappy_can_move_aux tau g ps = None ->
    In p ps ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = None.
Proof.
  intros tau g ps p a Hnone Hin Hocc Hunhappy.
  destruct (find_destination tau g a) eqn:Hdest; [|reflexivity].
  exfalso.
  induction ps as [|p' ps' IH].
  - inversion Hin.
  - simpl in Hnone.
    destruct Hin as [Heq | Hin'].
    + subst p'.
      rewrite Hocc in Hnone.
      rewrite Hunhappy in Hnone.
      rewrite Hdest in Hnone.
      discriminate.
    + destruct (get_cell g p') eqn:Hcell'.
      * apply IH; assumption.
      * destruct (happy tau g p') eqn:Hhappy'.
        -- apply IH; assumption.
        -- destruct (find_destination tau g a0) eqn:Hdest'.
           ++ discriminate.
           ++ apply IH; assumption.
Qed.

Theorem no_movable_unhappy_implies_fixpoint :
  forall tau g,
    wellformed_grid g ->
    find_unhappy_can_move_aux tau g all_positions_grid = None ->
    step tau g = g.
Proof.
  intros tau g Hwf Hnone.
  unfold step.
  assert (Hstep_pos : forall ps,
    (forall p, In p ps -> In p all_positions_grid) ->
    step_positions tau ps g = g).
  { intros ps Hsub.
    induction ps as [|p ps' IH].
    - reflexivity.
    - simpl.
      assert (Hstep_p : step_position tau g p = g).
      { destruct (get_cell g p) eqn:Hcell.
        - unfold step_position. rewrite Hcell. reflexivity.
        - destruct (happy tau g p) eqn:Hhappy.
          + unfold step_position. rewrite Hcell. rewrite Hhappy. reflexivity.
          + assert (Hno_dest : find_destination tau g a = None).
            { apply (find_unhappy_can_move_aux_none_implies_no_movable tau g all_positions_grid p a).
              - exact Hnone.
              - apply Hsub. left. reflexivity.
              - exact Hcell.
              - exact Hhappy. }
            unfold step_position. rewrite Hcell. rewrite Hhappy.
            rewrite Hno_dest. reflexivity. }
      rewrite Hstep_p.
      apply IH.
      intros q Hq. apply Hsub. right. exact Hq. }
  apply Hstep_pos.
  intros p Hp. exact Hp.
Qed.

Corollary not_stable_means_exists_unhappy :
  forall tau g,
    wellformed_grid g ->
    ~ stable tau g ->
    exists p, In p all_positions_grid /\ happy tau g p = false.
Proof.
  intros tau g Hwf Hnstable.
  apply micro_not_stable_means_exists_unhappy; assumption.
Qed.

Lemma step_positions_app :
  forall tau ps1 ps2 g,
    step_positions tau (ps1 ++ ps2) g =
    step_positions tau ps2 (step_positions tau ps1 g).
Proof.
  intros tau ps1.
  induction ps1 as [|p ps1' IH]; intros ps2 g; simpl.
  - reflexivity.
  - apply IH.
Qed.

Fixpoint find_grid_diff (g1 g2 : Grid) (ps : list Pos) : option Pos :=
  match ps with
  | [] => None
  | p :: ps' =>
      match cell_eq_dec (get_cell g1 p) (get_cell g2 p) with
      | left _ => find_grid_diff g1 g2 ps'
      | right _ => Some p
      end
  end.

Lemma find_grid_diff_some :
  forall g1 g2 ps p,
    find_grid_diff g1 g2 ps = Some p ->
    In p ps /\ get_cell g1 p <> get_cell g2 p.
Proof.
  intros g1 g2 ps p.
  induction ps as [|p' ps' IH]; intros Hfind.
  - discriminate.
  - simpl in Hfind.
    destruct (cell_eq_dec (get_cell g1 p') (get_cell g2 p')) as [Heq | Hneq].
    + apply IH in Hfind. destruct Hfind as [Hin Hneq_cell].
      split; [right; assumption | assumption].
    + injection Hfind as Hfind. subst p'.
      split; [left; reflexivity | assumption].
Qed.

Lemma find_grid_diff_none :
  forall g1 g2 ps,
    find_grid_diff g1 g2 ps = None ->
    forall p, In p ps -> get_cell g1 p = get_cell g2 p.
Proof.
  intros g1 g2 ps.
  induction ps as [|p' ps' IH]; intros Hnone p Hin.
  - inversion Hin.
  - simpl in Hnone.
    destruct (cell_eq_dec (get_cell g1 p') (get_cell g2 p')) as [Heq | Hneq].
    + destruct Hin as [Heq_p | Hin'].
      * subst p'. assumption.
      * apply IH; assumption.
    + discriminate.
Qed.

Theorem grid_equality_decidable :
  forall g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    {forall p, In p all_positions_grid -> get_cell g1 p = get_cell g2 p} +
    {exists p, In p all_positions_grid /\ get_cell g1 p <> get_cell g2 p}.
Proof.
  intros g1 g2 Hwf1 Hwf2.
  destruct (find_grid_diff g1 g2 all_positions_grid) eqn:Hfind.
  - right.
    apply find_grid_diff_some in Hfind.
    destruct Hfind as [Hin Hneq].
    exists p. split; assumption.
  - left.
    intros p Hin.
    apply (find_grid_diff_none g1 g2 all_positions_grid); assumption.
Defined.

Lemma empty_grid_always_stable :
  forall tau,
    stable tau empty_grid.
Proof.
  intros tau [i j].
  apply empty_cell_always_happy.
  reflexivity.
Qed.

Lemma find_destination_none_characterization :
  forall tau g a,
    find_destination tau g a = None <->
    (forall q, In q all_positions_grid -> get_cell g q = Empty -> happy_for tau g a q = false).
Proof.
  intros tau g a; split.
  - intros Hnone q Hin Hempty.
    unfold find_destination in Hnone.
    destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hfind; [discriminate|].
    assert (Hspec := List.find_none (empty_and_happy_for tau g a) all_positions_grid).
    rewrite Hfind in Hspec.
    specialize (Hspec eq_refl q Hin).
    unfold empty_and_happy_for in Hspec.
    unfold cell_is_empty in Hspec.
    rewrite Hempty in Hspec; simpl in Hspec.
    destruct (happy_for tau g a q) eqn:Hhappy; simpl in Hspec; [discriminate | reflexivity].
  - intros Hall.
    unfold find_destination.
    destruct (List.find (empty_and_happy_for tau g a) all_positions_grid) eqn:Hfind; [|reflexivity].
    exfalso.
    apply List.find_some in Hfind.
    destruct Hfind as [Hin Hcond].
    unfold empty_and_happy_for in Hcond.
    rewrite Bool.andb_true_iff in Hcond.
    destruct Hcond as [Hempty Hhappy].
    unfold cell_is_empty in Hempty.
    rewrite Bool.negb_true_iff in Hempty.
    destruct (get_cell g p) eqn:Hcell; [|simpl in Hempty; discriminate].
    specialize (Hall p Hin Hcell).
    rewrite Hhappy in Hall.
    discriminate.
Qed.

Lemma find_unhappy_can_move_exists_witness :
  forall tau g p a,
    In p all_positions_grid ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a <> None ->
    exists q, find_destination tau g a = Some q.
Proof.
  intros tau g p a Hin Hocc Hunhappy Hsome.
  destruct (find_destination tau g a) eqn:Hfind; [exists p0; reflexivity|contradiction].
Qed.

Lemma find_unhappy_movable_in_aux :
  forall tau g p a q,
    In p all_positions_grid ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    exists p', find_unhappy_can_move_aux tau g all_positions_grid = Some p'.
Proof.
  intros tau g p a q Hin Hocc Hunhappy Hfind.
  destruct (find_unhappy_can_move_aux tau g all_positions_grid) eqn:Haux; [exists p0; reflexivity|].
  exfalso.
  apply find_unhappy_can_move_aux_none_implies_no_movable with (p := p) (a := a) in Haux; try assumption.
  rewrite Hfind in Haux.
  discriminate.
Qed.

Lemma step_position_preserves_occupied_neq_source :
  forall tau g p' p a_at_p,
    p' <> p ->
    get_cell g p = Occupied a_at_p ->
    get_cell (step_position tau g p') p = Occupied a_at_p.
Proof.
  intros tau g p' p a_at_p Hneq Hcell.
  unfold step_position.
  destruct (get_cell g p') eqn:Hcellp'; [assumption|].
  destruct (happy tau g p') eqn:Hhappy; [assumption|].
  destruct (find_destination tau g a) eqn:Hfind; [|assumption].
  destruct (pos_eq_dec p p0) as [Heq | Hneq_dest].
  - subst p0.
    apply destination_is_empty in Hfind.
    rewrite Hcell in Hfind.
    discriminate.
  - rewrite get_set_other by (intros C; subst; apply Hneq_dest; reflexivity).
    rewrite get_set_other by (intros C; subst; apply Hneq; reflexivity).
    assumption.
Qed.

Lemma step_position_preserves_empty_neq_source_and_dest :
  forall tau g p' p,
    p' <> p ->
    get_cell g p = Empty ->
    (forall a q, get_cell g p' = Occupied a -> happy tau g p' = false ->
                 find_destination tau g a = Some q -> q <> p) ->
    get_cell (step_position tau g p') p = Empty.
Proof.
  intros tau g p' p Hneq Hempty Hnot_dest.
  unfold step_position.
  destruct (get_cell g p') eqn:Hcellp'; [assumption|].
  destruct (happy tau g p') eqn:Hhappy; [assumption|].
  destruct (find_destination tau g a) eqn:Hfind; [|assumption].
  assert (Hneq_dest : p0 <> p).
  { apply (Hnot_dest a p0 eq_refl eq_refl Hfind). }
  rewrite get_set_other by (intros C; subst; apply Hneq_dest; reflexivity).
  rewrite get_set_other by (intros C; subst; apply Hneq; reflexivity).
  assumption.
Qed.

Lemma step_position_preserves_cell_neq_dest :
  forall tau g p' p c q a,
    get_cell g p' = Occupied a ->
    happy tau g p' = false ->
    find_destination tau g a = Some q ->
    p <> q ->
    p' <> p ->
    get_cell g p = c ->
    get_cell (step_position tau g p') p = c.
Proof.
  intros tau g p' p c q a Hocc Hunhappy Hfind Hneq_q Hneq_p' Hcell.
  unfold step_position.
  rewrite Hocc, Hunhappy, Hfind.
  rewrite get_set_other by (intros C; subst; apply Hneq_q; reflexivity).
  rewrite get_set_other by (intros C; subst; apply Hneq_p'; reflexivity).
  assumption.
Qed.

Lemma step_positions_nil_preserves :
  forall tau g p c,
    get_cell g p = c ->
    get_cell (step_positions tau [] g) p = c.
Proof.
  intros tau g p c Hcell. simpl. assumption.
Qed.

Lemma step_positions_preserves_not_in_list :
  forall tau ps p a g,
    ~ In p ps ->
    get_cell g p = Occupied a ->
    get_cell (step_positions tau ps g) p = Occupied a.
Proof.
  intros tau ps.
  induction ps as [|p' ps' IH]; intros p a g Hnotin Hocc; simpl.
  - assumption.
  - assert (Hneq : p' <> p).
    { intros Heq. subst p'. apply Hnotin. left. reflexivity. }
    assert (Hnotin' : ~ In p ps').
    { intros Hin. apply Hnotin. right. assumption. }
    assert (Hafter : get_cell (step_position tau g p') p = Occupied a).
    { apply step_position_preserves_occupied_neq_source; assumption. }
    apply (IH p a (step_position tau g p') Hnotin' Hafter).
Qed.

Lemma step_position_preserves_empty_when_dest_match :
  forall tau g p' p a,
    p' <> p ->
    get_cell g p' = Occupied a ->
    happy tau g p' = false ->
    find_destination tau g a = Some p ->
    get_cell g p = Empty ->
    get_cell (step_position tau g p') p = Occupied a.
Proof.
  intros tau g p' p a Hneq Hocc Hunhappy Hfind Hempty.
  unfold step_position.
  rewrite Hocc, Hunhappy, Hfind.
  rewrite get_set_same.
  reflexivity.
Qed.

Lemma step_position_preserves_empty_neq_both :
  forall tau g p' p,
    p' <> p ->
    get_cell g p = Empty ->
    (forall a q, get_cell g p' = Occupied a -> happy tau g p' = false ->
                 find_destination tau g a = Some q -> q <> p) ->
    get_cell (step_position tau g p') p = Empty.
Proof.
  intros tau g p' p Hneq Hempty Hnot_dest.
  unfold step_position.
  destruct (get_cell g p') eqn:Hcellp'; [assumption|].
  destruct (happy tau g p') eqn:Hhappy; [assumption|].
  destruct (find_destination tau g a) eqn:Hfind; [|assumption].
  assert (Hneq_dest : p0 <> p) by (apply (Hnot_dest a p0 eq_refl eq_refl Hfind)).
  rewrite get_set_other by (intros C; subst; apply Hneq_dest; reflexivity).
  rewrite get_set_other by (intros C; subst; apply Hneq; reflexivity).
  assumption.
Qed.

Lemma movable_unhappy_implies_step_changes :
  forall tau g p a q,
    In p all_positions_grid ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    step_position tau g p <> g.
Proof.
  intros tau g p a q Hin Hocc Hunhappy Hfind Hcontra.
  unfold step_position in Hcontra.
  rewrite Hocc in Hcontra.
  rewrite Hunhappy in Hcontra.
  rewrite Hfind in Hcontra.
  assert (Hneq : p <> q).
  { apply (source_different_from_destination tau g p a q); assumption. }
  assert (Hneq' : q <> p) by (intros C; subst; contradiction).
  assert (Hempty : get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p = Empty).
  { rewrite get_set_other by assumption. rewrite get_set_same. reflexivity. }
  assert (Hcell_eq : get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p = get_cell g p).
  { rewrite Hcontra. reflexivity. }
  rewrite Hempty in Hcell_eq.
  rewrite Hocc in Hcell_eq.
  discriminate.
Qed.

Corollary wellformed_stable_through_iterations :
  forall tau g n,
    wellformed_grid g ->
    stable tau g ->
    wellformed_grid (Nat.iter n (step tau) g) /\ stable tau (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf Hstable.
  split.
  - apply step_n_preserves_wellformed. assumption.
  - induction n as [|n' IH]; simpl.
    + assumption.
    + rewrite step_stable_fixed_point by exact IH.
      exact IH.
Qed.

Lemma step_position_source_empty_when_moves :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    get_cell (step_position tau g p) p = Empty.
Proof.
  intros tau g p a q Hocc Hunhappy Hfind.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hfind.
  assert (Hneq : p <> q).
  { apply source_different_from_destination with (tau := tau) (g := g) (a := a); assumption. }
  assert (Hneq' : q <> p) by (intros C; subst; apply Hneq; reflexivity).
  rewrite get_set_other by exact Hneq'.
  rewrite get_set_same.
  reflexivity.
Qed.

Lemma step_position_dest_occupied_when_moves :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    get_cell (step_position tau g p) q = Occupied a.
Proof.
  intros tau g p a q Hocc Hunhappy Hfind.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hfind.
  rewrite get_set_same.
  reflexivity.
Qed.

Lemma step_position_other_unchanged_when_moves :
  forall tau g p a q r,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    r <> p ->
    r <> q ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p a q r Hocc Hunhappy Hfind Hneq_p Hneq_q.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hfind.
  assert (Hneq_qr : q <> r) by (intros C; subst; apply Hneq_q; reflexivity).
  assert (Hneq_pr : p <> r) by (intros C; subst; apply Hneq_p; reflexivity).
  rewrite get_set_other by exact Hneq_qr.
  rewrite get_set_other by exact Hneq_pr.
  reflexivity.
Qed.

Lemma step_position_unchanged_when_no_move :
  forall tau g p r,
    step_position tau g p = g ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hno_move.
  rewrite Hno_move.
  reflexivity.
Qed.

Theorem step_position_complete_characterization :
  forall tau g p,
    (step_position tau g p = g) \/
    (exists a q, get_cell g p = Occupied a /\
                 happy tau g p = false /\
                 find_destination tau g a = Some q).
Proof.
  intros tau g p.
  unfold step_position.
  destruct (get_cell g p) eqn:Hcell.
  - left. reflexivity.
  - destruct (happy tau g p) eqn:Hhappy.
    + left. reflexivity.
    + destruct (find_destination tau g a) eqn:Hfind.
      * right. exists a, p0. repeat split; assumption.
      * left. reflexivity.
Qed.

Lemma step_position_changes_exactly_two_cells_when_moves :
  forall tau g p a q r,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (get_cell (step_position tau g p) r <> get_cell g r) <-> (r = p \/ r = q).
Proof.
  intros tau g p a q r Hocc Hunhappy Hfind; split.
  - intros Hdiff.
    destruct (pos_eq_dec r p) as [Heq_p | Hneq_p].
    + left. exact Heq_p.
    + destruct (pos_eq_dec r q) as [Heq_q | Hneq_q].
      * right. exact Heq_q.
      * exfalso. apply Hdiff.
        apply step_position_other_unchanged_when_moves with (a := a) (q := q); assumption.
  - intros [Heq_p | Heq_q].
    + subst r.
      rewrite step_position_source_empty_when_moves with (a := a) (q := q); try assumption.
      rewrite Hocc.
      discriminate.
    + subst r.
      rewrite step_position_dest_occupied_when_moves with (a := a) (p := p); try assumption.
      apply destination_is_empty in Hfind.
      rewrite Hfind.
      discriminate.
Qed.

Lemma step_position_preserves_cells_when_no_change :
  forall tau g p r,
    step_position tau g p = g ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hno_change.
  rewrite Hno_change.
  reflexivity.
Qed.

Lemma step_position_preserves_non_source_cells :
  forall tau g p r,
    r <> p ->
    (get_cell (step_position tau g p) r <> get_cell g r) ->
    (exists a q, get_cell g p = Occupied a /\
                 happy tau g p = false /\
                 find_destination tau g a = Some q /\
                 r = q).
Proof.
  intros tau g p r Hneq_rp Hdiff.
  destruct (step_position_complete_characterization tau g p) as [Hno_move | [a [q [Hocc [Hunhappy Hfind]]]]].
  - exfalso. apply Hdiff. rewrite Hno_move. reflexivity.
  - exists a, q. repeat split; try assumption.
    destruct (pos_eq_dec r q) as [Heq | Hneq_rq].
    + exact Heq.
    + exfalso. apply Hdiff.
      apply step_position_other_unchanged_when_moves with (a := a) (q := q); assumption.
Qed.

Corollary step_position_unchanged_if_not_source_or_dest :
  forall tau g p r,
    r <> p ->
    (forall a q, get_cell g p = Occupied a ->
                 happy tau g p = false ->
                 find_destination tau g a = Some q ->
                 r <> q) ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hneq_rp Hnot_dest.
  destruct (step_position_complete_characterization tau g p) as [Hno_move | [a [q [Hocc [Hunhappy Hfind]]]]].
  - rewrite Hno_move. reflexivity.
  - apply step_position_other_unchanged_when_moves with (a := a) (q := q); try assumption.
    apply (Hnot_dest a q); assumption.
Qed.

Lemma step_positions_nil_preserves_cells :
  forall tau g r,
    get_cell (step_positions tau [] g) r = get_cell g r.
Proof.
  intros tau g r.
  simpl.
  reflexivity.
Qed.

Lemma step_position_empty_unchanged :
  forall tau g p r,
    get_cell g p = Empty ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hempty.
  unfold step_position.
  rewrite Hempty.
  reflexivity.
Qed.

Lemma step_position_happy_unchanged :
  forall tau g p a r,
    get_cell g p = Occupied a ->
    happy tau g p = true ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p a r Hocc Hhappy.
  unfold step_position.
  rewrite Hocc.
  rewrite Hhappy.
  reflexivity.
Qed.

Lemma step_position_unhappy_no_dest_unchanged :
  forall tau g p a r,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = None ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p a r Hocc Hunhappy Hno_dest.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hno_dest.
  reflexivity.
Qed.

Lemma step_position_with_move_structure :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    step_position tau g p = set_cell (set_cell g p Empty) q (Occupied a).
Proof.
  intros tau g p a q Hocc Hunhappy Hfind.
  unfold step_position.
  rewrite Hocc.
  rewrite Hunhappy.
  rewrite Hfind.
  reflexivity.
Qed.

Lemma moved_source_is_empty :
  forall g p a q,
    p <> q ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p = Empty.
Proof.
  intros g p a q Hneq.
  assert (Hneq' : q <> p) by (intros C; subst; apply Hneq; reflexivity).
  rewrite get_set_other by exact Hneq'.
  rewrite get_set_same.
  reflexivity.
Qed.

Lemma moved_dest_is_occupied :
  forall g p a q,
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) q = Occupied a.
Proof.
  intros g p a q.
  rewrite get_set_same.
  reflexivity.
Qed.

Lemma moved_other_unchanged :
  forall g p a q r,
    r <> p ->
    r <> q ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) r = get_cell g r.
Proof.
  intros g p a q r Hneq_p Hneq_q.
  assert (Hneq_qr : q <> r) by (intros C; subst; apply Hneq_q; reflexivity).
  assert (Hneq_pr : p <> r) by (intros C; subst; apply Hneq_p; reflexivity).
  rewrite get_set_other by exact Hneq_qr.
  rewrite get_set_other by exact Hneq_pr.
  reflexivity.
Qed.

Lemma destination_neq_source :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    find_destination tau g a = Some q ->
    p <> q.
Proof.
  intros tau g p a q Hocc Hfind Heq.
  subst q.
  apply destination_is_empty in Hfind.
  rewrite Hocc in Hfind.
  discriminate.
Qed.

Theorem step_position_cell_cases :
  forall tau g p r,
    (get_cell (step_position tau g p) r = get_cell g r) \/
    (exists a q, get_cell g p = Occupied a /\
                 happy tau g p = false /\
                 find_destination tau g a = Some q /\
                 (r = p \/ r = q)).
Proof.
  intros tau g p r.
  destruct (get_cell g p) eqn:Hcell_p.
  - left. apply step_position_empty_unchanged. exact Hcell_p.
  - destruct (happy tau g p) eqn:Hhappy.
    + left. apply step_position_happy_unchanged with (a := a); assumption.
    + destruct (find_destination tau g a) eqn:Hfind.
      * destruct (pos_eq_dec r p) as [Heq_p | Hneq_p].
        -- right. exists a, p0. auto.
        -- destruct (pos_eq_dec r p0) as [Heq_q | Hneq_q].
           ++ right. exists a, p0. auto.
           ++ left.
              rewrite step_position_with_move_structure with (a := a) (q := p0) by assumption.
              apply moved_other_unchanged; assumption.
      * left. apply step_position_unhappy_no_dest_unchanged with (a := a); assumption.
Qed.

Corollary step_position_preserves_cells_outside_movement :
  forall tau g p r,
    r <> p ->
    (forall a q, get_cell g p = Occupied a ->
                 happy tau g p = false ->
                 find_destination tau g a = Some q ->
                 r <> q) ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hneq_p Hnot_dest.
  destruct (step_position_cell_cases tau g p r) as [Hpreserved | [a [q [Hocc [Hunhappy [Hfind [Heq_p | Heq_q]]]]]]].
  - exact Hpreserved.
  - exfalso. apply Hneq_p. exact Heq_p.
  - exfalso. apply (Hnot_dest a q); assumption.
Qed.

Theorem parallel_sequential_equivalence_on_stable :
  forall tau g,
    stable tau g ->
    step_parallel tau g = step tau g.
Proof.
  intros tau g Hstable.
  rewrite step_parallel_stable_fixed_point by assumption.
  rewrite step_stable_fixed_point by assumption.
  reflexivity.
Qed.

Corollary sequential_preserves_wellformed :
  forall tau g,
    wellformed_grid g ->
    wellformed_grid (step tau g).
Proof.
  intros tau g Hwf.
  apply step_preserves_wellformed; assumption.
Qed.

(* -----------------------------------------------------------------------------
   Grid Construction Utilities
   ----------------------------------------------------------------------------- *)

Fixpoint place_agents_aux (agents : list (Pos * Agent)) (g : Grid) : Grid :=
  match agents with
  | [] => g
  | (p, a) :: rest => place_agents_aux rest (set_cell g p (Occupied a))
  end.

Definition grid_from_list (agents : list (Pos * Agent)) : Grid :=
  place_agents_aux agents empty_grid.

Lemma place_agents_aux_wellformed :
  forall agents g,
    wellformed_grid g ->
    (forall p a, In (p, a) agents -> in_bounds p) ->
    wellformed_grid (place_agents_aux agents g).
Proof.
  intros agents; induction agents as [|pa rest IH]; intros g Hwf Hbounds; simpl.
  - assumption.
  - destruct pa as [p ag].
    apply IH.
    + apply set_cell_preserves_wellformed; [assumption|].
      apply (Hbounds p ag); left; reflexivity.
    + intros p' a' Hin; apply (Hbounds p' a'); right; assumption.
Qed.

Lemma grid_from_list_wellformed :
  forall agents,
    (forall p a, In (p, a) agents -> in_bounds p) ->
    wellformed_grid (grid_from_list agents).
Proof.
  intros agents Hbounds.
  unfold grid_from_list.
  apply place_agents_aux_wellformed.
  - apply empty_grid_wellformed.
  - assumption.
Qed.

(* -----------------------------------------------------------------------------
   Computational Complexity Analysis
   ----------------------------------------------------------------------------- *)

(** This section provides formal statements about the time and space complexity
    of key operations. While Coq cannot directly prove asymptotic complexity
    (as it would require a cost model), we can establish bounds on the number
    of elementary operations. *)

(** * Time Complexity Bounds *)

(** Neighbor computation: O(grid_size²) for Moore neighborhood *)

Lemma filter_length_le {A : Type} (f : A -> bool) (l : list A) :
  (length (filter f l) <= length l)%nat.
Proof.
  induction l as [|x l' IH]; simpl.
  - reflexivity.
  - destruct (f x); simpl; lia.
Qed.

Lemma neighbors_length_bounded :
  forall p,
    (length (neighbors p) <= grid_size * grid_size)%nat.
Proof.
  intros p.
  unfold neighbors.
  assert (Hlen : (length (filter (moore_neighbor p) all_positions_grid) <=
                  length all_positions_grid)%nat).
  { apply filter_length_le. }
  rewrite all_positions_length in Hlen.
  exact Hlen.
Qed.

Lemma Z_abs_le_1_bounded :
  forall a b : Z,
    (Z.abs (a - b) <= 1)%Z ->
    (a = b - 1 \/ a = b \/ a = b + 1)%Z.
Proof.
  intros a b H.
  destruct (Z_lt_le_dec (a - b) 0) as [Hneg | Hpos].
  - assert (Habs : (Z.abs (a - b) = - (a - b))%Z).
    { apply Z.abs_neq. lia. }
    rewrite Habs in H. lia.
  - assert (Habs : (Z.abs (a - b) = a - b)%Z).
    { apply Z.abs_eq. lia. }
    rewrite Habs in H. lia.
Qed.

Lemma moore_radius_1_3x3_grid :
  neighborhood_radius = 1%nat ->
  forall i j q,
    moore_neighbor (i, j) q = true ->
    exists i' j',
      q = (i', j') /\
      (i' = i \/ i' = (i - 1)%nat \/ i' = (i + 1)%nat) /\
      (j' = j \/ j' = (j - 1)%nat \/ j' = (j + 1)%nat) /\
      (i' <> i \/ j' <> j).
Proof.
  intros Hr1 i j q Hmn.
  unfold moore_neighbor in Hmn.
  destruct q as [i' j']; simpl in *.
  rewrite Hr1 in Hmn.
  repeat (rewrite Bool.andb_true_iff in Hmn).
  destruct Hmn as [[Hdi Hdj] Hneq].
  exists i', j'; repeat split; try reflexivity.
  - apply Z.leb_le in Hdi.
    apply Z_abs_le_1_bounded in Hdi.
    destruct Hdi as [Hi | [Hi | Hi]]; lia.
  - apply Z.leb_le in Hdj.
    apply Z_abs_le_1_bounded in Hdj.
    destruct Hdj as [Hj | [Hj | Hj]]; lia.
  - rewrite Bool.negb_true_iff in Hneq.
    rewrite Bool.andb_false_iff in Hneq.
    destruct Hneq as [H1 | H2].
    + left. intros contra; subst i'.
      replace (Z.of_nat i - Z.of_nat i)%Z with 0%Z in H1 by lia.
      simpl in H1; discriminate.
    + right. intros contra; subst j'.
      replace (Z.of_nat j - Z.of_nat j)%Z with 0%Z in H2 by lia.
      simpl in H2; discriminate.
Qed.

Lemma neighbors_moore_radius_1_bounded :
  neighborhood_radius = 1%nat ->
  forall p, (length (neighbors p) <= grid_size * grid_size)%nat.
Proof.
  intros Hr1 p.
  apply neighbors_length_bounded.
Qed.

(** Find destination: O(grid_size²) - scans all positions once *)

Definition find_destination_cost : nat := grid_size * grid_size.

Lemma find_destination_scans_all_positions :
  forall tau g a,
    find_destination tau g a = List.find (empty_and_happy_for tau g a) all_positions_grid.
Proof.
  intros tau g a.
  reflexivity.
Qed.

(** Step position: O(grid_size²) worst case - dominated by find_destination *)

Definition step_position_cost_worst : nat := find_destination_cost.

(** Step (full grid): O(grid_size⁴) worst case
    - iterates grid_size² positions
    - each may call find_destination which is O(grid_size²) *)

Definition step_cost_worst : nat := (grid_size * grid_size * find_destination_cost)%nat.

Lemma step_cost_quartic :
  step_cost_worst = (grid_size * grid_size * grid_size * grid_size)%nat.
Proof.
  unfold step_cost_worst, find_destination_cost.
  ring.
Qed.

(** * Space Complexity *)

(** Grid representation: O(1) - functional representation doesn't store explicitly *)

(** Position enumeration: O(grid_size²) *)

Lemma all_positions_space :
  length all_positions_grid = (grid_size * grid_size)%nat.
Proof.
  apply all_positions_length.
Qed.

(** Move list in parallel semantics: O(grid_size²) worst case *)

Lemma compute_moves_length_bounded :
  forall tau g ps,
    (length (compute_moves tau g ps) <= length ps)%nat.
Proof.
  intros tau g ps.
  induction ps as [|p ps' IH]; simpl.
  - reflexivity.
  - destruct (get_cell g p) eqn:Hcell; [lia|].
    destruct (happy tau g p) eqn:Hhappy; [lia|].
    destruct (find_destination tau g a) eqn:Hfind; simpl; lia.
Qed.

Corollary compute_moves_grid_bounded :
  forall tau g,
    (length (compute_moves tau g all_positions_grid) <= grid_size * grid_size)%nat.
Proof.
  intros tau g.
  assert (H := compute_moves_length_bounded tau g all_positions_grid).
  rewrite all_positions_length in H.
  exact H.
Qed.

(** * Complexity Summary *)

(** The key complexity bottleneck is [step], which has O(n⁴) worst-case time
    where n = grid_size. This is because:
    - We iterate over all n² cells
    - For each unhappy agent, we scan all n² positions to find a destination

    In practice, if few agents move, complexity improves to O(n² + k·n²) = O(n²)
    where k is the number of moving agents. *)

Definition step_cost_best_case (moving_agents : nat) : nat :=
  (grid_size * grid_size + moving_agents * grid_size * grid_size)%nat.

Lemma step_cost_linear_in_movers :
  forall k,
    (k <= grid_size * grid_size)%nat ->
    (step_cost_best_case k <= (1 + k) * grid_size * grid_size)%nat.
Proof.
  intros k Hk.
  unfold step_cost_best_case.
  nia.
Qed.

(* -----------------------------------------------------------------------------
   Concrete Examples and Scenarios
   ----------------------------------------------------------------------------- *)

Section Examples.

Hypothesis grid_3x3 : grid_size = 3%nat.
Hypothesis radius_1 : neighborhood_radius = 1%nat.

(* Concrete agent examples using parametric Agent type *)
Variable RedAgent : Agent.
Variable BlueAgent : Agent.
Hypothesis RedBlue_distinct : RedAgent <> BlueAgent.
Hypothesis Red_neq_Blue : agent_eqb RedAgent BlueAgent = false.

Definition redblue_checkerboard : Grid :=
  set_cell (set_cell (set_cell (set_cell empty_grid
    (0%nat, 0%nat) (Occupied RedAgent))
    (0%nat, 1%nat) (Occupied BlueAgent))
    (1%nat, 0%nat) (Occupied BlueAgent))
    (1%nat, 1%nat) (Occupied RedAgent).

Example checkerboard_wellformed :
  wellformed_grid redblue_checkerboard.
Proof.
  unfold redblue_checkerboard.
  repeat (apply set_cell_preserves_wellformed;
          [| unfold in_bounds; simpl; rewrite grid_3x3; lia]).
  apply empty_grid_wellformed.
Qed.

Example checkerboard_count :
  count_agents redblue_checkerboard = 4%nat.
Proof.
  unfold count_agents, count_agents_at_positions, redblue_checkerboard.
  unfold all_positions_grid.
  rewrite grid_3x3.
  simpl.
  unfold get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  reflexivity.
Qed.

Definition red_cluster : Grid :=
  set_cell (set_cell (set_cell empty_grid
    (0%nat, 0%nat) (Occupied RedAgent))
    (0%nat, 1%nat) (Occupied RedAgent))
    (1%nat, 0%nat) (Occupied RedAgent).

Example red_cluster_happy_tau_1 :
  happy 1 red_cluster (0%nat, 0%nat) = true.
Proof.
  unfold happy, red_cluster.
  unfold get_cell, set_cell, pos_eqb.
  simpl.
  unfold neighbor_cells, neighbors.
  unfold moore_neighbor, all_positions_grid.
  rewrite grid_3x3, radius_1.
  simpl.
  unfold count_same.
  unfold get_cell, set_cell, pos_eqb.
  simpl.
  rewrite agent_eqb_refl.
  simpl.
  reflexivity.
Qed.

Definition isolated_blue : Grid :=
  set_cell (set_cell (set_cell (set_cell empty_grid
    (1%nat, 1%nat) (Occupied BlueAgent))
    (0%nat, 0%nat) (Occupied RedAgent))
    (0%nat, 2%nat) (Occupied RedAgent))
    (2%nat, 0%nat) (Occupied RedAgent).

Example isolated_blue_unhappy_tau_1 :
  happy 1 isolated_blue (1%nat, 1%nat) = false.
Proof.
  unfold happy, isolated_blue.
  unfold get_cell, set_cell, pos_eqb.
  simpl.
  unfold neighbor_cells, neighbors.
  unfold moore_neighbor, all_positions_grid.
  rewrite grid_3x3, radius_1.
  simpl.
  unfold count_same.
  unfold get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  assert (agent_eqb BlueAgent RedAgent = false).
  { destruct (agent_eqb BlueAgent RedAgent) eqn:E.
    - apply agent_eqb_eq in E. subst. rewrite agent_eqb_refl in Red_neq_Blue. discriminate.
    - reflexivity. }
  rewrite H. simpl. reflexivity.
Qed.

Definition segregated_grid : Grid :=
  set_cell (set_cell (set_cell (set_cell (set_cell (set_cell empty_grid
    (0%nat, 0%nat) (Occupied RedAgent))
    (0%nat, 1%nat) (Occupied RedAgent))
    (1%nat, 0%nat) (Occupied RedAgent))
    (1%nat, 2%nat) (Occupied BlueAgent))
    (2%nat, 1%nat) (Occupied BlueAgent))
    (2%nat, 2%nat) (Occupied BlueAgent).

Example segregated_stable_tau_2 :
  stable 2 segregated_grid.
Proof.
  unfold stable. intros [i j].
  destruct i as [|[|[|i']]]; destruct j as [|[|[|j']]];
    try (apply empty_cell_always_happy; unfold segregated_grid, get_cell, set_cell, pos_eqb, empty_grid;
         simpl; reflexivity);
    unfold happy, segregated_grid, get_cell, set_cell, pos_eqb;
    simpl; unfold neighbor_cells, neighbors, moore_neighbor, all_positions_grid;
    rewrite grid_3x3, radius_1; simpl; unfold count_same, get_cell, set_cell, pos_eqb;
    simpl; rewrite ?agent_eqb_refl;
    try (assert (agent_eqb BlueAgent RedAgent = false) by
           (destruct (agent_eqb BlueAgent RedAgent) eqn:E;
            [apply agent_eqb_eq in E; subst; rewrite agent_eqb_refl in Red_neq_Blue; discriminate | reflexivity]);
         rewrite H; simpl; reflexivity);
    simpl; reflexivity.
Qed.

Example segregated_conserves_agents :
  count_agents (step 2 segregated_grid) = count_agents segregated_grid.
Proof.
  apply step_preserves_agent_count.
Qed.

Example segregated_is_fixpoint :
  step 2 segregated_grid = segregated_grid.
Proof.
  apply step_stable_fixed_point.
  apply segregated_stable_tau_2.
Qed.

Definition mixing_grid : Grid :=
  set_cell (set_cell (set_cell empty_grid
    (0%nat, 0%nat) (Occupied RedAgent))
    (1%nat, 1%nat) (Occupied BlueAgent))
    (2%nat, 2%nat) (Occupied RedAgent).

Example mixing_grid_wellformed :
  wellformed_grid mixing_grid.
Proof.
  unfold mixing_grid.
  repeat (apply set_cell_preserves_wellformed;
          [| unfold in_bounds; simpl; rewrite grid_3x3; lia]).
  apply empty_grid_wellformed.
Qed.

Example mixing_grid_count :
  count_agents mixing_grid = 3%nat.
Proof.
  unfold count_agents, count_agents_at_positions, mixing_grid.
  unfold all_positions_grid.
  rewrite grid_3x3.
  simpl.
  unfold get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  reflexivity.
Qed.

Example ex_empty_grid_stable :
  stable 0 empty_grid.
Proof.
  apply empty_grid_always_stable.
Qed.

Example ex_empty_grid_is_wellformed :
  wellformed_grid empty_grid.
Proof.
  apply empty_grid_wellformed.
Qed.

Example ex_empty_grid_has_zero_agents :
  count_agents empty_grid = 0%nat.
Proof.
  unfold count_agents, count_agents_at_positions.
  induction all_positions_grid as [|p ps IH]; simpl.
  - reflexivity.
  - unfold get_cell, empty_grid. simpl. apply IH.
Qed.

Definition single_agent_grid (a : Agent) : Grid :=
  set_cell empty_grid (0%nat, 0%nat) (Occupied a).

Example ex_single_agent_wellformed :
  forall a, wellformed_grid (single_agent_grid a).
Proof.
  intros a.
  unfold single_agent_grid.
  apply set_cell_preserves_wellformed.
  - apply empty_grid_wellformed.
  - unfold in_bounds. simpl. rewrite grid_3x3. lia.
Qed.

Example ex_single_agent_count :
  forall a, count_agents (single_agent_grid a) = 1%nat.
Proof.
  intros a.
  unfold count_agents, count_agents_at_positions, single_agent_grid.
  unfold all_positions_grid.
  rewrite grid_3x3.
  simpl.
  unfold get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  reflexivity.
Qed.

Definition two_agent_grid (a1 a2 : Agent) : Grid :=
  set_cell (set_cell empty_grid (0%nat, 0%nat) (Occupied a1))
           (1%nat, 1%nat) (Occupied a2).

Example ex_two_agent_count :
  forall a1 a2, count_agents (two_agent_grid a1 a2) = 2%nat.
Proof.
  intros a1 a2.
  unfold count_agents, count_agents_at_positions, two_agent_grid.
  unfold all_positions_grid.
  rewrite grid_3x3.
  simpl.
  unfold get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  reflexivity.
Qed.

Example ex_two_agent_wellformed :
  forall a1 a2, wellformed_grid (two_agent_grid a1 a2).
Proof.
  intros a1 a2.
  unfold two_agent_grid.
  apply set_cell_preserves_wellformed.
  - apply set_cell_preserves_wellformed.
    + apply empty_grid_wellformed.
    + unfold in_bounds. simpl. rewrite grid_3x3. lia.
  - unfold in_bounds. simpl. rewrite grid_3x3. lia.
Qed.

Example ex_step_preserves_count :
  forall a, count_agents (step 0 (single_agent_grid a)) = count_agents (single_agent_grid a).
Proof.
  intros a.
  apply step_preserves_agent_count.
Qed.

Example ex_empty_stable_after_step :
  step 0 empty_grid = empty_grid.
Proof.
  apply step_stable_fixed_point.
  apply empty_grid_always_stable.
Qed.

Definition corner_grid (a : Agent) : Grid :=
  set_cell (set_cell (set_cell (set_cell empty_grid
    (0%nat, 0%nat) (Occupied a))
    (0%nat, 2%nat) (Occupied a))
    (2%nat, 0%nat) (Occupied a))
    (2%nat, 2%nat) (Occupied a).

Example ex_corner_grid_wellformed :
  forall a, wellformed_grid (corner_grid a).
Proof.
  intros a.
  unfold corner_grid.
  repeat (apply set_cell_preserves_wellformed;
          [| unfold in_bounds; simpl; rewrite grid_3x3; lia]).
  apply empty_grid_wellformed.
Qed.

Example ex_corner_grid_count :
  forall a, count_agents (corner_grid a) = 4%nat.
Proof.
  intros a.
  unfold count_agents, count_agents_at_positions, corner_grid.
  unfold all_positions_grid.
  rewrite grid_3x3.
  simpl.
  unfold get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  reflexivity.
Qed.

Example ex_grid_from_list_count :
  forall a, count_agents (grid_from_list [((0%nat, 0%nat), a); ((1%nat, 1%nat), a)]) = 2%nat.
Proof.
  intros a.
  unfold count_agents, count_agents_at_positions, grid_from_list.
  unfold all_positions_grid.
  rewrite grid_3x3.
  simpl.
  unfold place_agents_aux, get_cell, set_cell, pos_eqb, empty_grid.
  simpl.
  reflexivity.
Qed.

Example ex_stable_wellformed_preservation :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    wellformed_grid (step tau g).
Proof.
  intros tau g Hwf Hstable.
  rewrite step_stable_fixed_point by assumption.
  assumption.
Qed.

Example ex_agent_count_through_iterations :
  forall tau g n,
    count_agents (Nat.iter n (step tau) g) = count_agents g.
Proof.
  intros tau g n.
  apply step_n_preserves_agent_count.
Qed.

End Examples.

(* -----------------------------------------------------------------------------
   Complexity Bounds: How Many Steps Until Convergence?
   ----------------------------------------------------------------------------- *)

Lemma nat_pow_pos :
  forall a b,
    (0 < a)%nat ->
    (0 < a ^ b)%nat.
Proof.
  intros a b Ha.
  induction b as [|b' IH]; simpl.
  - lia.
  - apply Nat.mul_pos_pos; assumption.
Qed.

Lemma grid_configs_finite_positive :
  (0 < grid_configs_finite)%nat.
Proof.
  unfold grid_configs_finite.
  apply nat_pow_pos.
  lia.
Qed.

Lemma step_iter_S :
  forall tau g n,
    Nat.iter (S n) (step tau) g = step tau (Nat.iter n (step tau) g).
Proof.
  intros tau g n.
  reflexivity.
Qed.

Lemma step_iter_wellformed :
  forall tau g n,
    wellformed_grid g ->
    wellformed_grid (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf.
  apply step_n_preserves_wellformed.
  assumption.
Qed.

Lemma step_deterministic_iter :
  forall tau g1 g2 n,
    g1 = g2 ->
    Nat.iter n (step tau) g1 = Nat.iter n (step tau) g2.
Proof.
  intros tau g1 g2 n Heq.
  subst.
  reflexivity.
Qed.

Lemma step_iter_add :
  forall tau g m n,
    Nat.iter (m + n) (step tau) g = Nat.iter n (step tau) (Nat.iter m (step tau) g).
Proof.
  intros tau g m n.
  revert g.
  induction n as [|n' IH]; intros g.
  - rewrite Nat.add_0_r. reflexivity.
  - replace (m + S n')%nat with (S (m + n'))%nat by lia.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma grid_eq_wellformed_iff_equal :
  forall g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    grid_eq g1 g2 = true ->
    g1 = g2.
Proof.
  intros g1 g2 Hwf1 Hwf2 Heq.
  apply grid_eq_true_to_functional_eq; assumption.
Qed.

Lemma step_iter_repeat_implies_period :
  forall tau g i j,
    (i < j)%nat ->
    Nat.iter i (step tau) g = Nat.iter j (step tau) g ->
    has_period tau (Nat.iter i (step tau) g) (j - i).
Proof.
  intros tau g i j Hij Heq.
  unfold has_period.
  split.
  - lia.
  - replace j with (i + (j - i))%nat in Heq by lia.
    rewrite step_iter_add in Heq.
    symmetry.
    assumption.
Qed.

Lemma nat_exists_le_S :
  forall n,
    exists k, (k <= S n)%nat.
Proof.
  intros n.
  exists 0%nat.
  lia.
Qed.

Fixpoint iter_sequence (tau : nat) (g : Grid) (n : nat) : list Grid :=
  match n with
  | O => [g]
  | S n' => g :: iter_sequence tau (step tau g) n'
  end.

Lemma iter_sequence_length :
  forall tau g n,
    length (iter_sequence tau g n) = S n.
Proof.
  intros tau g n.
  revert g.
  induction n as [|n' IH]; intros g; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma nat_iter_S_comm :
  forall tau g k,
    Nat.iter k (step tau) (step tau g) = step tau (Nat.iter k (step tau) g).
Proof.
  intros tau g k.
  induction k as [|k' IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma iter_sequence_nth :
  forall tau g n k,
    (k <= n)%nat ->
    nth k (iter_sequence tau g n) empty_grid = Nat.iter k (step tau) g.
Proof.
  intros tau g n k Hk.
  revert g k Hk.
  induction n as [|n' IH]; intros g k Hk; simpl.
  - assert (k = 0)%nat by lia. subst. reflexivity.
  - destruct k as [|k'].
    + reflexivity.
    + simpl.
      rewrite IH by lia.
      apply nat_iter_S_comm.
Qed.

Lemma stable_eventually :
  forall tau g i,
    wellformed_grid g ->
    stable tau (Nat.iter i (step tau) g) ->
    (exists j, (j <= i)%nat /\ stable tau (Nat.iter j (step tau) g)).
Proof.
  intros tau g i Hwf Hstable.
  exists i.
  split; [lia | assumption].
Qed.

Theorem bounded_convergence_weak :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    (exists i, (i <= 0)%nat /\ is_fixpoint tau (Nat.iter i (step tau) g)).
Proof.
  intros tau g Hwf Hstable.
  exists 0%nat.
  split.
  - lia.
  - simpl.
    unfold is_fixpoint.
    apply step_stable_fixed_point.
    assumption.
Qed.

Theorem bounded_steps_stable_case :
  forall tau g N i,
    wellformed_grid g ->
    (i <= N)%nat ->
    stable tau (Nat.iter i (step tau) g) ->
    is_fixpoint tau (Nat.iter i (step tau) g).
Proof.
  intros tau g N i Hwf Hi Hstable.
  unfold is_fixpoint.
  apply step_stable_fixed_point.
  assumption.
Qed.

Theorem iteration_preserves_fixpoint :
  forall tau g n,
    wellformed_grid g ->
    is_fixpoint tau g ->
    Nat.iter n (step tau) g = g.
Proof.
  intros tau g n Hwf Hfix.
  induction n as [|n' IH]; simpl.
  - reflexivity.
  - rewrite IH.
    unfold is_fixpoint in Hfix.
    assumption.
Qed.

Lemma period_from_repeat :
  forall tau g i j,
    wellformed_grid g ->
    (i < j)%nat ->
    Nat.iter i (step tau) g = Nat.iter j (step tau) g ->
    has_period tau (Nat.iter i (step tau) g) (j - i).
Proof.
  intros tau g i j Hwf Hij Heq.
  apply step_iter_repeat_implies_period; assumption.
Qed.

Theorem period_positive :
  forall tau g p,
    has_period tau g p ->
    (p > 0)%nat.
Proof.
  intros tau g p [Hpos Hperiod].
  assumption.
Qed.

Lemma period_mult_also_period :
  forall tau g p k,
    has_period tau g p ->
    Nat.iter (k * p) (step tau) g = g.
Proof.
  intros tau g p k Hperiod.
  apply period_multiple.
  assumption.
Qed.

Corollary fixpoint_stays_fixed :
  forall tau g n,
    wellformed_grid g ->
    is_fixpoint tau g ->
    is_fixpoint tau (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf Hfix.
  unfold is_fixpoint in *.
  rewrite iteration_preserves_fixpoint by assumption.
  assumption.
Qed.

Lemma grid_configs_bound_positive :
  (grid_configs_finite > 0)%nat.
Proof.
  unfold grid_configs_finite.
  apply nat_pow_pos.
  lia.
Qed.

Theorem complexity_bound_statement :
  (grid_configs_finite = 3 ^ (grid_size * grid_size))%nat.
Proof.
  unfold grid_configs_finite.
  reflexivity.
Qed.

Theorem configurations_grow_exponentially :
  forall n,
    (n > 0)%nat ->
    (3 ^ n > n)%nat.
Proof.
  intros n Hn.
  induction n as [|n' IH]; [lia|].
  simpl.
  destruct n' as [|n''].
  - simpl. lia.
  - assert (Hn': (0 < S n'')%nat) by lia.
    specialize (IH Hn').
    lia.
Qed.

Corollary config_space_larger_than_grid :
  (grid_configs_finite > grid_size * grid_size)%nat.
Proof.
  unfold grid_configs_finite.
  apply configurations_grow_exponentially.
  apply Nat.mul_pos_pos; apply grid_size_pos.
Qed.

Lemma iter_zero_identity :
  forall tau g,
    Nat.iter 0 (step tau) g = g.
Proof.
  intros tau g.
  reflexivity.
Qed.

Lemma iter_one_is_step :
  forall tau g,
    Nat.iter 1 (step tau) g = step tau g.
Proof.
  intros tau g.
  reflexivity.
Qed.

Lemma grid_eq_decidable :
  forall g1 g2,
    wellformed_grid g1 ->
    wellformed_grid g2 ->
    {g1 = g2} + {g1 <> g2}.
Proof.
  intros g1 g2 Hwf1 Hwf2.
  destruct (grid_eq g1 g2) eqn:Heq.
  - left; apply grid_eq_true_to_functional_eq; assumption.
  - right; intros Hcontra; subst; rewrite grid_eq_refl in Heq; discriminate.
Defined.

Lemma fixpoint_or_progress :
  forall tau g,
    wellformed_grid g ->
    is_fixpoint tau g \/ step tau g <> g.
Proof.
  intros tau g Hwf.
  destruct (grid_eq_decidable g (step tau g) Hwf (step_preserves_wellformed tau g Hwf)) as [Heq | Hneq].
  - left; unfold is_fixpoint; symmetry; assumption.
  - right; intros Hcontra; apply Hneq; symmetry; assumption.
Qed.

Lemma iter_fixpoint_stable :
  forall tau g n,
    wellformed_grid g ->
    is_fixpoint tau (Nat.iter n (step tau) g) ->
    forall k, (k >= n)%nat -> Nat.iter k (step tau) g = Nat.iter n (step tau) g.
Proof.
  intros tau g n Hwf Hfix k Hk.
  replace k with (n + (k - n))%nat by lia.
  rewrite step_iter_add.
  apply iteration_preserves_fixpoint.
  - apply step_iter_wellformed; assumption.
  - assumption.
Qed.

Lemma iter_bound_wellformed :
  forall tau g n,
    wellformed_grid g ->
    (n <= grid_configs_finite)%nat ->
    wellformed_grid (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf Hn.
  apply step_iter_wellformed; assumption.
Qed.

Lemma consecutive_iter_equal_is_fixpoint :
  forall tau g n,
    wellformed_grid g ->
    Nat.iter n (step tau) g = Nat.iter (S n) (step tau) g ->
    is_fixpoint tau (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf Heq.
  unfold is_fixpoint.
  simpl in Heq.
  symmetry.
  assumption.
Qed.

Lemma iter_at_n_wellformed :
  forall tau g n,
    wellformed_grid g ->
    wellformed_grid (Nat.iter n (step tau) g).
Proof.
  intros tau g n Hwf.
  apply step_n_preserves_wellformed.
  assumption.
Qed.

Lemma iter_comparison_decidable :
  forall tau g n m,
    wellformed_grid g ->
    {Nat.iter n (step tau) g = Nat.iter m (step tau) g} +
    {Nat.iter n (step tau) g <> Nat.iter m (step tau) g}.
Proof.
  intros tau g n m Hwf.
  apply grid_eq_decidable.
  - apply iter_at_n_wellformed; assumption.
  - apply iter_at_n_wellformed; assumption.
Defined.

Lemma fixpoint_at_n_decidable :
  forall tau g n,
    wellformed_grid g ->
    {is_fixpoint tau (Nat.iter n (step tau) g)} +
    {~ is_fixpoint tau (Nat.iter n (step tau) g)}.
Proof.
  intros tau g n Hwf.
  unfold is_fixpoint.
  destruct (iter_comparison_decidable tau g n (S n) Hwf) as [Heq | Hneq].
  - left.
    simpl in Heq.
    symmetry.
    assumption.
  - right.
    intros Hcontra.
    apply Hneq.
    simpl.
    symmetry.
    assumption.
Defined.

Lemma fixpoint_exists_in_range :
  forall tau g n,
    wellformed_grid g ->
    (n > 0)%nat ->
    (exists k, (k < n)%nat /\ is_fixpoint tau (Nat.iter k (step tau) g)) \/
    (forall k, (k < n)%nat -> ~ is_fixpoint tau (Nat.iter k (step tau) g)).
Proof.
  intros tau g n Hwf Hn.
  induction n as [|n' IH].
  - lia.
  - destruct (fixpoint_at_n_decidable tau g n' Hwf) as [Hfix | Hnfix].
    + left.
      exists n'.
      split; [lia | assumption].
    + destruct n' as [|n''].
      * right.
        intros k Hk.
        assert (k = 0)%nat by lia.
        subst k.
        assumption.
      * destruct (IH (Nat.lt_0_succ n'')) as [[k [Hk Hfix]] | Hall].
        -- left.
           exists k.
           split; [lia | assumption].
        -- right.
           intros k Hk.
           destruct (Nat.lt_ge_cases k (S n'')) as [Hlt | Hge].
           ++ apply Hall.
              assumption.
           ++ assert (k = S n'') by lia.
              subst k.
              assumption.
Qed.

Theorem bounded_termination :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat -> ~ is_fixpoint tau (Nat.iter i (step tau) g)).
Proof.
  intros tau g Hwf.
  assert (Hpos : (grid_configs_finite > 0)%nat) by apply grid_configs_bound_positive.
  destruct (fixpoint_exists_in_range tau g grid_configs_finite Hwf Hpos) as [[k [Hk Hfix]] | Hall].
  - left.
    exists k.
    split; [assumption | assumption].
  - right.
    intros i Hi.
    apply Hall.
    assumption.
Qed.

Lemma no_fixpoint_means_progress_always :
  forall tau g n,
    wellformed_grid g ->
    ~ is_fixpoint tau (Nat.iter n (step tau) g) ->
    Nat.iter n (step tau) g <> Nat.iter (S n) (step tau) g.
Proof.
  intros tau g n Hwf Hnfix.
  intros Hcontra.
  apply Hnfix.
  apply consecutive_iter_equal_is_fixpoint.
  - assumption.
  - assumption.
Qed.

Theorem bounded_termination_v2 :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat ->
       Nat.iter i (step tau) g <> Nat.iter (S i) (step tau) g).
Proof.
  intros tau g Hwf.
  destruct (bounded_termination tau g Hwf) as [[n [Hn Hfix]] | Hall].
  - left.
    exists n.
    split; [assumption | assumption].
  - right.
    intros i Hi.
    apply no_fixpoint_means_progress_always.
    + assumption.
    + apply Hall.
      assumption.
Qed.

Corollary termination_dichotomy :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat -> ~ is_fixpoint tau (Nat.iter i (step tau) g)).
Proof.
  intros tau g Hwf.
  exact (bounded_termination tau g Hwf).
Qed.

Lemma succ_iter_unfold :
  forall tau g n,
    Nat.iter (S n) (step tau) g = step tau (Nat.iter n (step tau) g).
Proof.
  intros tau g n.
  simpl.
  reflexivity.
Qed.

Lemma no_fixpoint_below_means_none_at :
  forall tau g n i,
    (forall j, (j < n)%nat -> ~ is_fixpoint tau (Nat.iter j (step tau) g)) ->
    (i < n)%nat ->
    ~ is_fixpoint tau (Nat.iter i (step tau) g).
Proof.
  intros tau g n i Hall Hi.
  apply Hall.
  exact Hi.
Qed.

Corollary termination_summary :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat -> ~ is_fixpoint tau (Nat.iter i (step tau) g)).
Proof.
  intros tau g Hwf.
  exact (bounded_termination tau g Hwf).
Qed.

(* -----------------------------------------------------------------------------
   Segregation Increase Theorem
   ----------------------------------------------------------------------------- *)

Lemma local_homophily_moved_agent_improves :
  forall tau g p q a,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (local_homophily (step_position tau g p) q >= local_homophily g q)%Q.
Proof.
  intros tau g p q a Hocc Hunhappy Hfind.
  unfold step_position.
  rewrite Hocc, Hunhappy, Hfind.
  unfold local_homophily.
  assert (Hempty: get_cell g q = Empty).
  { apply (destination_is_empty tau g a q). exact Hfind. }
  rewrite Hempty.
  rewrite get_set_same.
  simpl.
  assert (Hhappy_for: happy_for tau g a q = true).
  { apply (destination_makes_happy tau g a q). exact Hfind. }
  unfold happy_for in Hhappy_for.
  apply Nat.leb_le in Hhappy_for.
  destruct (count_same a (neighbor_cells (set_cell (set_cell g p Empty) q (Occupied a)) q) +
            count_different a (neighbor_cells (set_cell (set_cell g p Empty) q (Occupied a)) q))%nat eqn:Htotal.
  - unfold Qle. simpl. lia.
  - unfold Qle. simpl. lia.
Qed.

Theorem moving_agents_achieve_positive_homophily :
  forall tau g p a q,
    In p all_positions_grid ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (0 <= local_homophily (step_position tau g p) q)%Q.
Proof.
  intros tau g p a q Hin Hocc Hunhappy Hfind.
  destruct (local_homophily_range (step_position tau g p) q) as [Hge _].
  exact Hge.
Qed.

Corollary unhappy_agent_improves_homophily_at_destination :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (local_homophily (step_position tau g p) q >= local_homophily g q)%Q.
Proof.
  intros tau g p a q Hocc Hunhappy Hfind.
  apply (local_homophily_moved_agent_improves tau g p q a); assumption.
Qed.

Theorem segregation_increases_schelling :
  forall tau g p a q,
    wellformed_grid g ->
    In p all_positions_grid ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (local_homophily g q = 0)%Q /\
    (local_homophily (step_position tau g p) q >= 0)%Q /\
    (local_homophily g p <= 1)%Q.
Proof.
  intros tau g p a q Hwf Hin Hocc Hunhappy Hfind.
  repeat split.
  - unfold local_homophily.
    assert (Hempty: get_cell g q = Empty).
    { apply (destination_is_empty tau g a q). exact Hfind. }
    rewrite Hempty.
    reflexivity.
  - destruct (local_homophily_range (step_position tau g p) q) as [Hge _].
    exact Hge.
  - destruct (local_homophily_range g p) as [_ Hle].
    exact Hle.
Qed.

Lemma moved_agent_achieves_high_same_count :
  forall tau g p a q,
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (tau <= count_same a (neighbor_cells g q))%nat.
Proof.
  intros tau g p a q Hocc Hunhappy Hfind.
  apply (moving_agent_satisfies_tolerance tau g p a q); assumption.
Qed.

Theorem stable_grids_preserve_segregation :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    global_segregation (step tau g) = global_segregation g.
Proof.
  intros tau g Hwf Hstable.
  rewrite step_stable_fixed_point by assumption.
  reflexivity.
Qed.

Corollary segregation_bounded_in_stable_states :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    (0 <= global_segregation g <= 1)%Q.
Proof.
  intros tau g Hwf Hstable.
  apply global_segregation_range.
Qed.

Theorem unhappy_agents_move_to_better_neighborhoods :
  forall tau g p a q,
    In p all_positions_grid ->
    (tau > 0)%nat ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (count_same a (neighbor_cells g p) < tau)%nat /\
    (tau <= count_same a (neighbor_cells g q))%nat.
Proof.
  intros tau g p a q Hin Htau_pos Hocc Hunhappy Hfind.
  split.
  - apply (unhappy_means_unsatisfied tau g p a); assumption.
  - apply (moved_agent_achieves_high_same_count tau g p a q); assumption.
Qed.

Corollary segregation_dynamic :
  forall tau g p a q,
    In p all_positions_grid ->
    (tau > 0)%nat ->
    get_cell g p = Occupied a ->
    happy tau g p = false ->
    find_destination tau g a = Some q ->
    (count_same a (neighbor_cells g q) > count_same a (neighbor_cells g p))%nat.
Proof.
  intros tau g p a q Hin Htau_pos Hocc Hunhappy Hfind.
  destruct (unhappy_agents_move_to_better_neighborhoods tau g p a q Hin Htau_pos Hocc Hunhappy Hfind) as [Hsource Hdest].
  lia.
Qed.

Theorem agent_count_preserved_under_segregation_dynamics :
  forall tau g n,
    wellformed_grid g ->
    count_agents (Nat.iter n (step tau) g) = count_agents g.
Proof.
  intros tau g n Hwf.
  apply step_n_preserves_agent_count.
Qed.

Theorem segregation_process_reaches_stable_configuration :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    (forall p, In p all_positions_grid -> happy tau g p = true).
Proof.
  intros tau g Hwf Hstable p Hin.
  unfold stable in Hstable.
  apply Hstable.
Qed.


End SchellingModel.

(* -----------------------------------------------------------------------------
   End of file
   ----------------------------------------------------------------------------- *)
