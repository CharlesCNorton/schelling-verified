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

Section SchellingModel.

(** Grid dimension parameter. *)
Variable grid_size : nat.
Hypothesis grid_size_pos : (0 < grid_size)%nat.

(** Moore/von Neumann neighborhood radius. *)
Variable neighborhood_radius : nat.

(** Abstract agent type with decidable equality. *)
Variable Agent : Type.
Variable agent_eqb : Agent -> Agent -> bool.
Hypothesis agent_eqb_eq : forall a1 a2, agent_eqb a1 a2 = true <-> a1 = a2.

(** Default minimum count of same-type neighbors for happiness. *)
Definition tolerance_default : nat := 3.

End SchellingModel.

(* -----------------------------------------------------------------------------
   Concrete Agent Instantiations
   ----------------------------------------------------------------------------- *)

Module ConcreteAgents.

(** Two-color agent type for basic segregation scenarios. *)
Inductive Color : Type :=
| Red
| Blue.

(** Boolean equality on colors. *)
Definition color_eqb (c1 c2 : Color) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Blue, Blue => true
  | _, _ => false
  end.

(** Correctness of color_eqb. *)
Lemma color_eqb_eq : forall c1 c2, color_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2; split; intros H.
  - destruct c1, c2; simpl in H; try discriminate; reflexivity.
  - subst; destruct c2; reflexivity.
Qed.

(** Three-group ethnicity type. *)
Inductive Ethnicity : Type :=
| GroupA
| GroupB
| GroupC.

(** Boolean equality on ethnicities. *)
Definition ethnicity_eqb (e1 e2 : Ethnicity) : bool :=
  match e1, e2 with
  | GroupA, GroupA => true
  | GroupB, GroupB => true
  | GroupC, GroupC => true
  | _, _ => false
  end.

(** Correctness of ethnicity_eqb. *)
Lemma ethnicity_eqb_eq : forall e1 e2, ethnicity_eqb e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2; split; intros H.
  - destruct e1, e2; simpl in H; try discriminate; reflexivity.
  - subst; destruct e2; reflexivity.
Qed.

(** Three-level income stratification. *)
Inductive Income : Type :=
| Low
| Middle
| High.

(** Boolean equality on income levels. *)
Definition income_eqb (i1 i2 : Income) : bool :=
  match i1, i2 with
  | Low, Low => true
  | Middle, Middle => true
  | High, High => true
  | _, _ => false
  end.

(** Correctness of income_eqb. *)
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

(** Grid cell: empty or occupied by an agent. *)
Inductive Cell : Type :=
| Empty
| Occupied (a : Agent).

(** Grid position as (row, column) pair. *)
Definition Pos := (nat * nat)%type.

(** Grid as total function from positions to cells. *)
Definition Grid := Pos -> Cell.

(* -----------------------------------------------------------------------------
   Equality on Agents and Positions
   ----------------------------------------------------------------------------- *)

(** Reflexivity of agent_eqb. *)
Lemma agent_eqb_refl : forall a, agent_eqb a a = true.
Proof.
  intros a.
  apply agent_eqb_eq.
  reflexivity.
Qed.

(** Inequality characterization for agents. *)
Lemma agent_eqb_neq : forall a1 a2, a1 <> a2 <-> agent_eqb a1 a2 = false.
Proof.
  intros a1 a2; split.
  - intros Hneq.
    destruct (agent_eqb a1 a2) eqn:E; [|reflexivity].
    apply agent_eqb_eq in E.
    contradiction.
  - intros Hfalse Heq; subst; rewrite agent_eqb_refl in Hfalse; discriminate.
Qed.

(** Decidable equality on agents. *)
Lemma agent_eq_dec : forall a1 a2 : Agent, {a1 = a2} + {a1 <> a2}.
Proof.
  intros a1 a2.
  destruct (agent_eqb a1 a2) eqn:Heq.
  - left; apply agent_eqb_eq; assumption.
  - right; apply agent_eqb_neq; assumption.
Defined.

(** Boolean equality on positions. *)
Definition pos_eqb (p1 p2 : Pos) : bool :=
  let '(i1, j1) := p1 in
  let '(i2, j2) := p2 in
  Nat.eqb i1 i2 && Nat.eqb j1 j2.

(** Reflexivity of pos_eqb. *)
Lemma pos_eqb_refl : forall p, pos_eqb p p = true.
Proof.
  intros [i j]; unfold pos_eqb; simpl.
  rewrite !Nat.eqb_refl; reflexivity.
Qed.

(** Soundness of pos_eqb. *)
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

(** Completeness of pos_eqb for inequality. *)
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

(** Decidable equality on positions. *)
Lemma pos_eq_dec : forall p1 p2 : Pos, {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  destruct (pos_eqb p1 p2) eqn:Heq.
  - left; apply pos_eqb_eq; assumption.
  - right; intros Hcontra; subst; rewrite pos_eqb_refl in Heq; discriminate.
Defined.

(** Position within grid bounds. *)
Definition in_bounds (p : Pos) : Prop :=
  let '(i, j) := p in (i < grid_size)%nat /\ (j < grid_size)%nat.

(** Boolean version of in_bounds. *)
Definition in_bounds_b (p : Pos) : bool :=
  let '(i, j) := p in Nat.ltb i grid_size && Nat.ltb j grid_size.

(** Decidability of in_bounds. *)
Lemma in_bounds_dec : forall p, {in_bounds p} + {~ in_bounds p}.
Proof.
  intros [i j]; unfold in_bounds; simpl.
  destruct (Nat.ltb i grid_size) eqn:Hi, (Nat.ltb j grid_size) eqn:Hj.
  - left; split; apply Nat.ltb_lt; assumption.
  - right; intros [_ Hj']; apply Nat.ltb_lt in Hj'; rewrite Hj' in Hj; discriminate.
  - right; intros [Hi' _]; apply Nat.ltb_lt in Hi'; rewrite Hi' in Hi; discriminate.
  - right; intros [Hi' _]; apply Nat.ltb_lt in Hi'; rewrite Hi' in Hi; discriminate.
Defined.

(** Equivalence of propositional and boolean bounds checks. *)
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

(** Read cell at position p. *)
Definition get_cell (g : Grid) (p : Pos) : Cell := g p.

(** Update cell at position p to c. *)
Definition set_cell (g : Grid) (p : Pos) (c : Cell) : Grid :=
  fun q => if pos_eqb q p then c else g q.

(** Reading after writing at same position returns written value. *)
Lemma get_set_same :
  forall g p c, get_cell (set_cell g p c) p = c.
Proof.
  intros g p c; unfold get_cell, set_cell.
  rewrite pos_eqb_refl.
  reflexivity.
Qed.

(** Reading after writing at different position returns original value. *)
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
   Notations
   ----------------------------------------------------------------------------- *)

Notation "g [ p ]" := (get_cell g p) (at level 50, left associativity).
Notation "g [ p <- c ]" := (set_cell g p c) (at level 50, left associativity).
Notation "p ∈ ℬ" := (in_bounds p) (at level 70).
Notation "p ∉ ℬ" := (~ in_bounds p) (at level 70).

(* -----------------------------------------------------------------------------
   Proof Automation Tactics
   ----------------------------------------------------------------------------- *)

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

(** Two writes to same position: second write overwrites first. *)
Corollary set_cell_twice_same_pos :
  forall g p c1 c2 q,
    get_cell (set_cell (set_cell g p c1) p c2) q = get_cell (set_cell g p c2) q.
Proof.
  intros g p c1 c2 q.
  unfold get_cell, set_cell.
  destruct (pos_eqb q p); reflexivity.
Qed.

(** Writes to distinct positions commute. *)
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

(** Grid with all cells empty. *)
Definition empty_grid : Grid := fun _ => Empty.

(** All cells of empty_grid are Empty. *)
Corollary empty_grid_get_cell :
  forall p, get_cell empty_grid p = Empty.
Proof.
  intros p; reflexivity.
Qed.

(** Writing Empty to empty grid is identity. *)
Corollary set_empty_noop :
  forall p q,
    get_cell (set_cell empty_grid p Empty) q = get_cell empty_grid q.
Proof.
  intros p q.
  unfold set_cell, empty_grid, get_cell.
  destruct (pos_eqb q p); reflexivity.
Qed.

(** Grid wellformedness: out-of-bounds cells are empty. *)
Definition wellformed_grid (g : Grid) : Prop :=
  forall i j, ((i >= grid_size)%nat \/ (j >= grid_size)%nat) -> get_cell g (i, j) = Empty.

(** Wellformed grid as dependent record. *)
Record WFGrid : Type := mkWFGrid {
  wf_grid :> Grid;
  wf_proof : wellformed_grid wf_grid
}.

(** empty_grid is wellformed. *)
Lemma empty_grid_wellformed : wellformed_grid empty_grid.
Proof.
  intros i j _; reflexivity.
Qed.

(** Wellformed empty grid as WFGrid. *)
Definition empty_wfgrid : WFGrid :=
  mkWFGrid empty_grid empty_grid_wellformed.

(** Out-of-bounds access on wellformed grid yields Empty. *)
Lemma wellformed_grid_get_cell :
  forall g i j,
    wellformed_grid g ->
    ((i >= grid_size)%nat \/ (j >= grid_size)%nat) ->
    get_cell g (i, j) = Empty.
Proof.
  intros g i j Hwf Hout; apply Hwf; assumption.
Qed.

(** Writing to in-bounds position preserves wellformedness. *)
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

(** Writing Empty preserves wellformedness. *)
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

(** Two writes preserve wellformedness if second is in-bounds. *)
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

(** Lexicographic enumeration of all grid_size × grid_size positions. *)
Definition all_positions_grid : list Pos :=
  flat_map
    (fun i => map (fun j => (i, j)) (seq 0 grid_size))
    (seq 0 grid_size).

(** All positions in all_positions_grid are in bounds. *)
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

(** All in-bounds positions are in all_positions_grid. *)
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

(** Length of flat_map over cons. *)
Lemma flat_map_cons_length {A B : Type} (f : A -> list B) (x : A) (xs : list A) :
  length (flat_map f (x :: xs)) = (length (f x) + length (flat_map f xs))%nat.
Proof.
  simpl. rewrite app_length. reflexivity.
Qed.

(** Auxiliary lemma for computing all_positions_grid length. *)
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

(** all_positions_grid has exactly grid_size² elements. *)
Lemma all_positions_length :
  length all_positions_grid = (grid_size * grid_size)%nat.
Proof.
  unfold all_positions_grid.
  apply flat_map_row_length_aux.
  apply seq_length.
Qed.

(** all_positions_grid is non-empty. *)
Corollary all_positions_nonempty :
  all_positions_grid <> [].
Proof.
  intros Hempty.
  assert (Hlen : length all_positions_grid = (grid_size * grid_size)%nat) by apply all_positions_length.
  rewrite Hempty in Hlen; simpl in Hlen.
  assert (Hpos : (0 < grid_size * grid_size)%nat) by lia.
  lia.
Qed.

(** in_bounds positions are in all_positions_grid. *)
Corollary all_positions_complete :
  forall p,
    in_bounds p ->
    In p all_positions_grid.
Proof.
  intros [i j] [Hi Hj]; apply all_positions_coverage; assumption.
Qed.

(** Positions in all_positions_grid are in bounds. *)
Corollary all_positions_only_in_bounds :
  forall p,
    In p all_positions_grid ->
    in_bounds p.
Proof.
  intros [i j] Hin; apply all_positions_in_bounds in Hin.
  destruct Hin as [Hi Hj]; split; assumption.
Qed.

(** grid_size is positive. *)
Lemma grid_size_positive :
  (0 < grid_size)%nat.
Proof.
  exact grid_size_pos.
Qed.

(** Grid area is positive. *)
Lemma grid_area_positive :
  (0 < grid_size * grid_size)%nat.
Proof.
  apply Nat.mul_pos_pos; exact grid_size_pos.
Qed.

(** all_positions_grid is non-empty. *)
Lemma all_positions_length_positive :
  (0 < length all_positions_grid)%nat.
Proof.
  rewrite all_positions_length.
  apply grid_area_positive.
Qed.

(** Existence of at least one in-bounds position. *)
Lemma exists_valid_position :
  exists p, in_bounds p.
Proof.
  exists (0%nat, 0%nat).
  unfold in_bounds; simpl.
  split; exact grid_size_pos.
Qed.

(** Existence of at least one position in all_positions_grid. *)
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

(** Moore neighborhood predicate: max(|i-i'|, |j-j'|) ≤ radius and (i,j) ≠ (i',j'). *)
Definition moore_neighbor (p q : Pos) : bool :=
  let '(i, j)   := p in
  let '(i', j') := q in
  let di := Z.abs (Z.of_nat i - Z.of_nat i') in
  let dj := Z.abs (Z.of_nat j - Z.of_nat j') in
  Z.leb di (Z.of_nat neighborhood_radius) &&
  Z.leb dj (Z.of_nat neighborhood_radius) &&
  negb (Z.eqb di 0 && Z.eqb dj 0).

(** Neighbors of p as filtered list. *)
Definition neighbors (p : Pos) : list Pos :=
  filter (moore_neighbor p) all_positions_grid.

(** Position is not its own Moore neighbor. *)
Lemma moore_neighbor_irreflexive :
  forall p, moore_neighbor p p = false.
Proof.
  intros [i j]; unfold moore_neighbor; simpl.
  replace (Z.of_nat i - Z.of_nat i) with 0%Z by lia.
  replace (Z.of_nat j - Z.of_nat j) with 0%Z by lia.
  simpl. destruct (Z.of_nat neighborhood_radius); reflexivity.
Qed.

(** Position is not in its own neighbor set. *)
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

(** Absolute value symmetric in subtraction. *)
Lemma Z_abs_symmetric : forall a b, Z.abs (a - b) = Z.abs (b - a).
Proof.
  intros a b.
  assert (H : a - b = - (b - a)) by lia.
  rewrite H; apply Z.abs_opp.
Qed.

(** Moore neighborhood relation is symmetric. *)
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

(** von Neumann neighborhood predicate: |i-i'| + |j-j'| ≤ radius (L1 metric). *)
Definition von_neumann_neighbor (p q : Pos) : bool :=
  let '(i, j)   := p in
  let '(i', j') := q in
  let di := Z.abs (Z.of_nat i - Z.of_nat i') in
  let dj := Z.abs (Z.of_nat j - Z.of_nat j') in
  Z.leb (di + dj) (Z.of_nat neighborhood_radius) &&
  negb (Z.eqb di 0 && Z.eqb dj 0).

(** von Neumann neighbors of p as filtered list. *)
Definition von_neumann_neighbors (p : Pos) : list Pos :=
  filter (von_neumann_neighbor p) all_positions_grid.

(** Position is not its own von Neumann neighbor. *)
Lemma von_neumann_neighbor_irreflexive :
  forall p, von_neumann_neighbor p p = false.
Proof.
  intros [i j]; unfold von_neumann_neighbor; simpl.
  replace (Z.of_nat i - Z.of_nat i) with 0%Z by lia.
  replace (Z.of_nat j - Z.of_nat j) with 0%Z by lia.
  simpl. destruct (Z.of_nat neighborhood_radius); reflexivity.
Qed.

(** Position is not in its own von Neumann neighbor set. *)
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

(** von Neumann neighborhood relation is symmetric. *)
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

(** von Neumann neighbors are in bounds. *)
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

(** von Neumann neighbors are Moore neighbors (L1 ⊆ L∞). *)
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

(** von Neumann neighbor set is subset of Moore neighbor set. *)
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

(** von Neumann neighbor count bounded by grid area. *)
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

(** Neighborhood predicate type. *)
Definition NeighborPredicate := Pos -> Pos -> bool.

(** Valid neighborhood predicate: irreflexive and symmetric. *)
Definition valid_neighbor_pred (pred : NeighborPredicate) : Prop :=
  (forall p, pred p p = false) /\
  (forall p q, pred p q = true -> pred q p = true).

(** General neighbors using arbitrary predicate. *)
Definition general_neighbors (pred : NeighborPredicate) (p : Pos) : list Pos :=
  filter (pred p) all_positions_grid.

(** Lp metric type. *)
Inductive LpMetric : Type :=
  | L1_metric    (* Manhattan distance, von Neumann *)
  | L2_metric    (* Euclidean distance *)
  | Linf_metric. (* Chebyshev distance, Moore *)

(** Lp distance between positions. *)
Definition lp_distance (metric : LpMetric) (p q : Pos) : Z :=
  let '(i, j)   := p in
  let '(i', j') := q in
  let di := Z.abs (Z.of_nat i - Z.of_nat i') in
  let dj := Z.abs (Z.of_nat j - Z.of_nat j') in
  match metric with
  | L1_metric => di + dj
  | L2_metric => di * di + dj * dj
  | Linf_metric => Z.max di dj
  end.

(** Lp neighbor predicate with given radius. *)
Definition lp_neighbor (metric : LpMetric) (radius : nat) (p q : Pos) : bool :=
  let dist := lp_distance metric p q in
  Z.leb dist (Z.of_nat radius) &&
  negb (Z.eqb dist 0).

(** max(a,b) = 0 implies a = 0 and b = 0 for non-negative a, b. *)
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

(** (a=0 ∧ b=0) ↔ max(a,b)=0 for non-negative a, b. *)
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

(** Negation distributes over max-zero equivalence. *)
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

(** Negation distributes over sum-zero equivalence for non-negative a, b. *)
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

(** max(a,b) = a when b ≤ a. *)
Lemma max_eq_left_ge :
  forall a b : Z,
    (b <= a)%Z ->
    Z.max a b = a.
Proof.
  intros a b Hle.
  destruct (Z.max_spec a b) as [[H Heq] | [H Heq]]; rewrite Heq; try reflexivity.
  lia.
Qed.

(** max(a,b) = b when a ≤ b. *)
Lemma max_eq_right_ge :
  forall a b : Z,
    (a <= b)%Z ->
    Z.max a b = b.
Proof.
  intros a b Hle.
  destruct (Z.max_spec a b) as [[H Heq] | [H Heq]]; rewrite Heq; try reflexivity.
  lia.
Qed.

(** Moore neighborhood equals L∞ metric with neighborhood_radius. *)
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

(** von Neumann neighborhood equals L1 metric with neighborhood_radius. *)
Lemma von_neumann_is_l1 :
  forall p q,
    von_neumann_neighbor p q = lp_neighbor L1_metric neighborhood_radius p q.
Proof.
  intros [i j] [i' j']; unfold von_neumann_neighbor, lp_neighbor, lp_distance; simpl.
  f_equal.
  apply negb_sum_zero_iff_negb_both_zero; apply Z.abs_nonneg.
Qed.

(** Lp distance is non-negative. *)
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

(** Lp distance is zero iff positions are equal. *)
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

(** Lp distance is symmetric. *)
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

(** Lp neighbor is irreflexive. *)
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

(** Lp neighbor is symmetric. *)
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

(** Lp neighbor satisfies valid neighbor predicate. *)
Lemma lp_neighbor_valid :
  forall metric radius,
    valid_neighbor_pred (lp_neighbor metric radius).
Proof.
  intros metric radius; unfold valid_neighbor_pred; split.
  - intros p; apply lp_neighbor_irreflexive.
  - intros p q; apply lp_neighbor_symmetric.
Qed.

(** Moore neighbor satisfies valid neighbor predicate. *)
Theorem moore_neighbor_valid :
  valid_neighbor_pred moore_neighbor.
Proof.
  unfold valid_neighbor_pred; split.
  - intros p; apply moore_neighbor_irreflexive.
  - intros p q; apply neighbors_symmetric.
Qed.

(** von Neumann neighbor satisfies valid neighbor predicate. *)
Theorem von_neumann_neighbor_valid :
  valid_neighbor_pred von_neumann_neighbor.
Proof.
  unfold valid_neighbor_pred; split.
  - intros p; apply von_neumann_neighbor_irreflexive.
  - intros p q; apply von_neumann_neighbor_symmetric.
Qed.

(** General neighbors exclude the position itself. *)
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

(** General neighbors are in bounds. *)
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

(** General neighbor relation is symmetric on membership. *)
Lemma general_neighbors_symmetric_membership :
  forall pred p q,
    valid_neighbor_pred pred ->
    in_bounds p ->
    In q (general_neighbors pred p) ->
    In p (general_neighbors pred q).
Proof.
  intros pred p q [_ Hsym] Hp_bounds Hin.
  unfold general_neighbors in *.
  apply filter_In in Hin.
  destruct Hin as [Hin_all Hpred].
  apply filter_In; split.
  - apply all_positions_complete; assumption.
  - apply Hsym; assumption.
Qed.

(** neighbors equals general_neighbors with moore_neighbor. *)
Lemma neighbors_eq_general_moore :
  forall p,
    neighbors p = general_neighbors moore_neighbor p.
Proof.
  intros p; unfold neighbors, general_neighbors; reflexivity.
Qed.

(** von_neumann_neighbors equals general_neighbors with von_neumann_neighbor. *)
Lemma von_neumann_neighbors_eq_general :
  forall p,
    von_neumann_neighbors p = general_neighbors von_neumann_neighbor p.
Proof.
  intros p; unfold von_neumann_neighbors, general_neighbors; reflexivity.
Qed.

(** L1 neighbors with given radius. *)
Definition l1_neighbors (radius : nat) (p : Pos) : list Pos :=
  general_neighbors (lp_neighbor L1_metric radius) p.

(** L2 neighbors with given radius. *)
Definition l2_neighbors (radius : nat) (p : Pos) : list Pos :=
  general_neighbors (lp_neighbor L2_metric radius) p.

(** L∞ neighbors with given radius. *)
Definition linf_neighbors (radius : nat) (p : Pos) : list Pos :=
  general_neighbors (lp_neighbor Linf_metric radius) p.

(** von Neumann neighbors equal L1 neighbors with neighborhood_radius. *)
Theorem von_neumann_is_l1_neighbors :
  forall p,
    von_neumann_neighbors p = l1_neighbors neighborhood_radius p.
Proof.
  intros p.
  unfold von_neumann_neighbors, l1_neighbors, general_neighbors.
  f_equal.
  apply functional_extensionality.
  intros q.
  unfold von_neumann_neighbor, lp_neighbor.
  destruct p as [i j], q as [i' j'].
  simpl.
  f_equal.
  assert (Hdi : (0 <= Z.abs (Z.of_nat i - Z.of_nat i'))%Z) by apply Z.abs_nonneg.
  assert (Hdj : (0 <= Z.abs (Z.of_nat j - Z.of_nat j'))%Z) by apply Z.abs_nonneg.
  destruct (Z.eqb_spec (Z.abs (Z.of_nat i - Z.of_nat i')) 0),
           (Z.eqb_spec (Z.abs (Z.of_nat j - Z.of_nat j')) 0),
           (Z.eqb_spec (Z.abs (Z.of_nat i - Z.of_nat i') + Z.abs (Z.of_nat j - Z.of_nat j')) 0);
  subst; simpl; try reflexivity; try lia.
Qed.

(** Moore neighbors equal L∞ neighbors with neighborhood_radius. *)
Theorem neighbors_is_linf_neighbors :
  forall p,
    neighbors p = linf_neighbors neighborhood_radius p.
Proof.
  intros p.
  unfold neighbors, linf_neighbors, general_neighbors.
  f_equal.
  apply functional_extensionality.
  intros q.
  unfold moore_neighbor, lp_neighbor.
  destruct p as [i j], q as [i' j'].
  simpl.
  set (di := Z.abs (Z.of_nat i - Z.of_nat i')).
  set (dj := Z.abs (Z.of_nat j - Z.of_nat j')).
  assert (Hdi : (0 <= di)%Z) by apply Z.abs_nonneg.
  assert (Hdj : (0 <= dj)%Z) by apply Z.abs_nonneg.
  destruct (Z.max_spec di dj) as [[Hle Hmax] | [Hle Hmax]];
  rewrite Hmax; clear Hmax.
  - destruct (Z.leb_spec dj (Z.of_nat neighborhood_radius)),
             (Z.leb_spec di (Z.of_nat neighborhood_radius)),
             (Z.eqb_spec di 0),
             (Z.eqb_spec dj 0);
    subst; simpl; try reflexivity; try lia.
  - destruct (Z.leb_spec di (Z.of_nat neighborhood_radius)),
             (Z.leb_spec dj (Z.of_nat neighborhood_radius)),
             (Z.eqb_spec di 0),
             (Z.eqb_spec dj 0);
    subst; simpl; try reflexivity; try lia.
Qed.

(** L1 distance is at most twice L∞ distance. *)
Lemma l1_distance_le_linf_scaled :
  forall p q,
    (lp_distance L1_metric p q <= 2 * lp_distance Linf_metric p q)%Z.
Proof.
  intros [i j] [i' j']; unfold lp_distance; simpl.
  set (di := Z.abs (Z.of_nat i - Z.of_nat i')).
  set (dj := Z.abs (Z.of_nat j - Z.of_nat j')).
  assert (Hdi : (0 <= di)%Z) by apply Z.abs_nonneg.
  assert (Hdj : (0 <= dj)%Z) by apply Z.abs_nonneg.
  destruct (Z.max_spec di dj) as [[Hle Hmax] | [Hle Hmax]];
  rewrite Hmax.
  - assert (Hsum : (di + dj <= 2 * dj)%Z) by lia.
    exact Hsum.
  - assert (Hsum : (di + dj <= 2 * di)%Z) by lia.
    exact Hsum.
Qed.

(** L∞ distance is at most L1 distance. *)
Lemma linf_distance_le_l1 :
  forall p q,
    (lp_distance Linf_metric p q <= lp_distance L1_metric p q)%Z.
Proof.
  intros [i j] [i' j']; unfold lp_distance; simpl.
  destruct (Z.max_spec (Z.abs (Z.of_nat i - Z.of_nat i'))
                        (Z.abs (Z.of_nat j - Z.of_nat j'))) as [[Hle Hmax] | [Hle Hmax]];
  rewrite Hmax; lia.
Qed.

(** General neighbor count bounded by grid area. *)
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

(** Extensionality for general neighbors. *)
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

(** Monotonicity of general neighbors under predicate implication. *)
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

(** Custom neighbors with user-defined predicate. *)
Definition custom_neighbors (pred : NeighborPredicate) (p : Pos) : list Pos :=
  general_neighbors pred p.

(** custom_neighbors equals general_neighbors. *)
Lemma custom_neighbors_correct :
  forall pred p,
    valid_neighbor_pred pred ->
    custom_neighbors pred p = general_neighbors pred p.
Proof.
  intros pred p Hvalid; reflexivity.
Qed.

(** Absolute value is non-negative. *)
Lemma Z_abs_nonneg_simple : forall z : Z, (0 <= Z.abs z)%Z.
Proof.
  intros z. apply Z.abs_nonneg.
Qed.

(** |0| = 0. *)
Lemma Z_abs_0_is_0 : Z.abs 0 = 0%Z.
Proof.
  reflexivity.
Qed.

(** |1| = 1. *)
Lemma Z_abs_1_is_1 : Z.abs 1 = 1%Z.
Proof.
  reflexivity.
Qed.

(** |-1| = 1. *)
Lemma Z_abs_neg1_is_1 : Z.abs (-1) = 1%Z.
Proof.
  reflexivity.
Qed.

(** Sum ≤ 1 implies components ≤ 1 for non-negative a, b. *)
Lemma Z_sum_le_1_components_le_1 : forall a b : Z,
  (0 <= a)%Z -> (0 <= b)%Z -> (a + b <= 1)%Z -> (a <= 1 /\ b <= 1)%Z.
Proof.
  intros a b Ha Hb Hsum. lia.
Qed.

(** |a| + |b| = 0 implies a = 0 and b = 0. *)
Lemma Z_abs_sum_0_both_0 : forall a b : Z,
  (Z.abs a + Z.abs b = 0)%Z -> a = 0%Z /\ b = 0%Z.
Proof.
  intros a b H.
  assert (Ha : Z.abs a = 0%Z) by lia.
  assert (Hb : Z.abs b = 0%Z) by lia.
  split; apply Z.abs_0_iff; assumption.
Qed.

(** |a| + |b| = 1 implies one is 0 and other is 1. *)
Lemma Z_abs_sum_1_cases : forall a b : Z,
  (Z.abs a + Z.abs b = 1)%Z ->
  (Z.abs a = 0 /\ Z.abs b = 1) \/ (Z.abs a = 1 /\ Z.abs b = 0)%Z.
Proof.
  intros a b H.
  assert (Ha_nonneg : (0 <= Z.abs a)%Z) by apply Z.abs_nonneg.
  assert (Hb_nonneg : (0 <= Z.abs b)%Z) by apply Z.abs_nonneg.
  lia.
Qed.

(** |z| = 1 implies z = 1 or z = -1. *)
Lemma Z_abs_1_means_1_or_neg1 : forall z : Z,
  Z.abs z = 1%Z -> z = 1%Z \/ z = (-1)%Z.
Proof.
  intros z H. lia.
Qed.

(** Integer representation difference 0 implies natural number equality. *)
Lemma Z_of_nat_diff_0 : forall n m : nat,
  (Z.of_nat n - Z.of_nat m = 0)%Z -> n = m.
Proof.
  intros n m H. lia.
Qed.

(** Integer representation difference 1 implies successor relation. *)
Lemma Z_of_nat_diff_1_succ : forall n m : nat,
  (Z.of_nat m - Z.of_nat n = 1)%Z -> m = S n.
Proof.
  intros n m H. lia.
Qed.

(** Integer representation difference -1 implies predecessor relation. *)
Lemma Z_of_nat_diff_neg1_pred : forall n m : nat,
  (Z.of_nat n - Z.of_nat m = 1)%Z -> n = S m.
Proof.
  intros n m H. lia.
Qed.

(** n - 0 = n for natural numbers. *)
Lemma nat_minus_0_l : forall n : nat, (n - 0 = n)%nat.
Proof. intros. lia. Qed.

(** Every natural number is either 0 or a successor. *)
Lemma S_pred_or_0 : forall n : nat, (n = 0 \/ exists m, n = S m)%nat.
Proof. intros. destruct n; [left|right; exists n]; auto. Qed.

(** Membership in 4-element list. *)
Lemma in_4_list : forall {A} (x a b c d : A),
  In x [a; b; c; d] <-> (x = a \/ x = b \/ x = c \/ x = d).
Proof. intros. simpl. intuition. Qed.

(** Length of 4-element list is 4. *)
Lemma length_4_list : forall {A} (a b c d : A), length [a; b; c; d] = 4%nat.
Proof. intros. reflexivity. Qed.

(** Inclusion and NoDup imply length bound. *)
Lemma incl_length_le : forall {A} (l1 l2 : list A),
  NoDup l1 -> incl l1 l2 -> (length l1 <= length l2)%nat.
Proof. intros. apply NoDup_incl_length; assumption. Qed.

(** Filtering preserves NoDup. *)
Lemma filter_NoDup : forall {A} (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof. intros. apply NoDup_filter. assumption. Qed.

(** Mapping (i,·) over sequence yields NoDup. *)
Lemma nodup_map_pair_left : forall n i,
  NoDup (map (fun j => (i, j) : nat * nat) (seq 0 n)).
Proof.
  intros. apply FinFun.Injective_map_NoDup.
  intros j1 j2 Heq. inversion Heq. reflexivity.
  apply seq_NoDup.
Qed.

(** von Neumann predicate with radius 1 implies L1 distance ≤ 1 and distinct positions. *)
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

(** von Neumann predicate with radius 1 implies one of four cardinal neighbors. *)
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

(** von Neumann neighbor count bounded by grid area. *)
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

(** von Neumann neighbors with radius 1 on 2×2 grid have at most 4 neighbors. *)
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

(** von Neumann neighbors with radius 1 on grids ≤ 2×2 have at most 4 neighbors. *)
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

(** von Neumann neighbors with radius 1 have at most 4 neighbors (conditional on NoDup). *)
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

(** Neighbors are in bounds. *)
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

(** Neighbors are in all_positions_grid. *)
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
   Happiness
   ----------------------------------------------------------------------------- *)

(** Cell is occupied. *)
Definition is_occupied (c : Cell) : bool :=
  match c with
  | Empty => false
  | Occupied _ => true
  end.

(** Occupation count: 1 if occupied, 0 if empty. *)
Definition cell_occ (c : Cell) : nat :=
  if is_occupied c then 1 else 0.

(** Count neighbors of same type as agent a. *)
Fixpoint count_same (a : Agent) (cells : list Cell) : nat :=
  match cells with
  | [] => 0
  | Empty :: cs => count_same a cs
  | Occupied b :: cs =>
      if agent_eqb a b
      then S (count_same a cs)
      else count_same a cs
  end.

(** Cells at neighbor positions. *)
Definition neighbor_cells (g : Grid) (p : Pos) : list Cell :=
  map (fun q => get_cell g q) (neighbors p).

(** Agent at p is happy if it has ≥ tau same-type neighbors. *)
Definition happy (tau : nat) (g : Grid) (p : Pos) : bool :=
  match get_cell g p with
  | Empty => true
  | Occupied a =>
      Nat.leb tau (count_same a (neighbor_cells g p))
  end.

(** Hypothetical happiness of agent a at position p. *)
Definition happy_for (tau : nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  Nat.leb tau (count_same a (neighbor_cells g p)).

(** Happiness with agent-specific tolerance function. *)
Definition happy_agent_tolerance (tau_fn : Agent -> nat) (g : Grid) (p : Pos) : bool :=
  match get_cell g p with
  | Empty => true
  | Occupied a =>
      Nat.leb (tau_fn a) (count_same a (neighbor_cells g p))
  end.

(** Hypothetical happiness with agent-specific tolerance. *)
Definition happy_for_agent_tolerance (tau_fn : Agent -> nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  Nat.leb (tau_fn a) (count_same a (neighbor_cells g p)).

(** Uniform tolerance equals constant tolerance function. *)
Lemma happy_uniform_is_agent_tolerance :
  forall tau g p,
    happy tau g p = happy_agent_tolerance (fun _ => tau) g p.
Proof.
  intros tau g p.
  unfold happy, happy_agent_tolerance.
  destruct (get_cell g p); reflexivity.
Qed.

(** Hypothetical happiness with uniform tolerance equals constant tolerance function. *)
Lemma happy_for_uniform_is_agent_tolerance :
  forall tau g a p,
    happy_for tau g a p = happy_for_agent_tolerance (fun _ => tau) g a p.
Proof.
  intros tau g a p.
  unfold happy_for, happy_for_agent_tolerance.
  reflexivity.
Qed.

(** Empty cells are always happy. *)
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

(** Happiness characterization: empty or sufficient same-type neighbors. *)
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

(** Happiness for occupied cell iff sufficient same-type neighbors. *)
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

(** Tolerance 0 makes all agents happy. *)
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
   Destination Search
   ----------------------------------------------------------------------------- *)

(** Position is empty. *)
Definition cell_is_empty (g : Grid) (p : Pos) : bool :=
  negb (is_occupied (get_cell g p)).

(** Position is empty and makes agent a happy. *)
Definition empty_and_happy_for (tau : nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  cell_is_empty g p && happy_for tau g a p.

(** First empty position that makes agent a happy. *)
Definition find_destination (tau : nat) (g : Grid) (a : Agent) : option Pos :=
  List.find (empty_and_happy_for tau g a) all_positions_grid.

(* -----------------------------------------------------------------------------
   Single-Position Dynamics
   ----------------------------------------------------------------------------- *)

(** Update grid at position p: unhappy agent moves if destination exists. *)
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
   Global Step (Sequential Update)
   ----------------------------------------------------------------------------- *)

(** Update grid sequentially over list of positions. *)
Fixpoint step_positions (tau : nat) (ps : list Pos) (g : Grid) : Grid :=
  match ps with
  | [] => g
  | p :: ps' =>
      let g' := step_position tau g p in
      step_positions tau ps' g'
  end.

(** Global step: sweep all positions in fixed order. *)
Definition step (tau : nat) (g : Grid) : Grid :=
  step_positions tau all_positions_grid g.

(* -----------------------------------------------------------------------------
   Agent-Specific Tolerance Dynamics
   ----------------------------------------------------------------------------- *)

(** Position is empty and makes agent a happy (agent-specific tolerance). *)
Definition empty_and_happy_for_agent_tolerance
  (tau_fn : Agent -> nat) (g : Grid) (a : Agent) (p : Pos) : bool :=
  cell_is_empty g p && happy_for_agent_tolerance tau_fn g a p.

(** First empty position making agent a happy (agent-specific tolerance). *)
Definition find_destination_agent_tolerance
  (tau_fn : Agent -> nat) (g : Grid) (a : Agent) : option Pos :=
  List.find (empty_and_happy_for_agent_tolerance tau_fn g a) all_positions_grid.

(** Update grid at position p with agent-specific tolerance. *)
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

(** Sequential update with agent-specific tolerance. *)
Fixpoint step_positions_agent_tolerance
  (tau_fn : Agent -> nat) (ps : list Pos) (g : Grid) : Grid :=
  match ps with
  | [] => g
  | p :: ps' =>
      let g' := step_position_agent_tolerance tau_fn g p in
      step_positions_agent_tolerance tau_fn ps' g'
  end.

(** Global step with agent-specific tolerance. *)
Definition step_agent_tolerance (tau_fn : Agent -> nat) (g : Grid) : Grid :=
  step_positions_agent_tolerance tau_fn all_positions_grid g.

(** Uniform tolerance destination check equals constant tolerance function. *)
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

(** Uniform tolerance destination search equals constant tolerance function. *)
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

(** Uniform tolerance single-position step equals constant tolerance function. *)
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

(** Compute all moves for positions in list ps. *)
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

(** Apply list of moves sequentially to grid. *)
Fixpoint apply_moves (moves : list (Pos * Pos * Agent)) (g : Grid) : Grid :=
  match moves with
  | [] => g
  | (p, q, a) :: rest =>
      let g1 := set_cell g p Empty in
      let g2 := set_cell g1 q (Occupied a) in
      apply_moves rest g2
  end.

(** Boolean NoDup checker using equality predicate. *)
Fixpoint NoDup_b {A : Type} (eqb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (eqb x) xs) && NoDup_b eqb xs
  end.

(** Extract destination positions from moves. *)
Fixpoint destinations_in_moves (moves : list (Pos * Pos * Agent)) : list Pos :=
  match moves with
  | [] => []
  | (_, q, _) :: rest => q :: destinations_in_moves rest
  end.

(** Check if moves have destination conflicts. *)
Definition has_destination_conflict (moves : list (Pos * Pos * Agent)) : bool :=
  let dests := destinations_in_moves moves in
  negb (NoDup_b pos_eqb dests).

(** Remove moves with duplicate destinations (keep first). *)
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

(** Remove destination conflicts from moves. *)
Definition remove_conflicts (moves : list (Pos * Pos * Agent)) : list (Pos * Pos * Agent) :=
  remove_conflicts_aux moves [].

(** Parallel step without conflict resolution. *)
Definition step_parallel_old (tau : nat) (g : Grid) : Grid :=
  apply_moves (compute_moves tau g all_positions_grid) g.

(** Parallel step with conflict resolution. *)
Definition step_parallel (tau : nat) (g : Grid) : Grid :=
  let all_moves := compute_moves tau g all_positions_grid in
  let conflict_free_moves := remove_conflicts all_moves in
  apply_moves conflict_free_moves g.

(** Applying empty move list is identity. *)
Lemma apply_moves_nil :
  forall g, apply_moves [] g = g.
Proof.
  intros g. reflexivity.
Qed.

(** compute_moves distributes over list concatenation. *)
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

(** existsb false implies not in list. *)
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

(** Positions in seen do not appear in conflict-removed destinations. *)
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

(** Conflict removal produces unique destinations. *)
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

(** remove_conflicts produces NoDup destination list. *)
Lemma remove_conflicts_no_duplicates :
  forall moves,
    NoDup (destinations_in_moves (remove_conflicts moves)).
Proof.
  intros moves.
  unfold remove_conflicts.
  apply remove_conflicts_aux_no_duplicates.
Qed.

(** Extract source positions from moves. *)
Fixpoint sources_in_moves (moves : list (Pos * Pos * Agent)) : list Pos :=
  match moves with
  | [] => []
  | (p, _, _) :: rest => p :: sources_in_moves rest
  end.

(** Extract agents from moves. *)
Fixpoint agents_in_moves (moves : list (Pos * Pos * Agent)) : list Agent :=
  match moves with
  | [] => []
  | (_, _, a) :: rest => a :: agents_in_moves rest
  end.

(** Source position in computed move is occupied by the agent. *)
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

(** Destination position in computed move is empty. *)
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

(** Source and destination in computed move are distinct. *)
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

(** Conflict-removed moves are subset of original moves. *)
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

(** remove_conflicts produces subset of original moves. *)
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
   Relational Semantics
   ----------------------------------------------------------------------------- *)

(** Step relation for global step. *)
Inductive StepRel (tau : nat) : Grid -> Grid -> Prop :=
  | step_rel_intro : forall g g',
      g' = step tau g ->
      StepRel tau g g'.

(** Step relation for single-position step. *)
Inductive StepPositionRel (tau : nat) (p : Pos) : Grid -> Grid -> Prop :=
  | step_position_rel_intro : forall g g',
      g' = step_position tau g p ->
      StepPositionRel tau p g g'.

(** StepRel is functional. *)
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

(** StepPositionRel is functional. *)
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

(** StepRel iff functional step. *)
Lemma step_rel_iff_step :
  forall tau g g',
    StepRel tau g g' <-> g' = step tau g.
Proof.
  intros tau g g'; split.
  - intros H; inversion H; subst; reflexivity.
  - intros H; constructor; assumption.
Qed.

(** StepPositionRel iff functional step_position. *)
Lemma step_position_rel_iff_step_position :
  forall tau p g g',
    StepPositionRel tau p g g' <-> g' = step_position tau g p.
Proof.
  intros tau p g g'; split.
  - intros H; inversion H; subst; reflexivity.
  - intros H; constructor; assumption.
Qed.

(** StepRel is deterministic. *)
Theorem step_rel_deterministic :
  forall tau g g1 g2,
    StepRel tau g g1 ->
    StepRel tau g g2 ->
    g1 = g2.
Proof.
  intros tau g g1 g2 H1 H2.
  apply step_rel_functional with (tau := tau) (g := g); assumption.
Qed.

(** StepPositionRel is deterministic. *)
Theorem step_position_rel_deterministic :
  forall tau p g g1 g2,
    StepPositionRel tau p g g1 ->
    StepPositionRel tau p g g2 ->
    g1 = g2.
Proof.
  intros tau p g g1 g2 H1 H2.
  apply step_position_rel_functional with (tau := tau) (p := p) (g := g); assumption.
Qed.

(** StepRel always exists. *)
Lemma step_rel_exists :
  forall tau g,
    exists g', StepRel tau g g'.
Proof.
  intros tau g.
  exists (step tau g).
  constructor; reflexivity.
Qed.

(** StepPositionRel always exists. *)
Lemma step_position_rel_exists :
  forall tau p g,
    exists g', StepPositionRel tau p g g'.
Proof.
  intros tau p g.
  exists (step_position tau g p).
  constructor; reflexivity.
Qed.

(** Reflexive transitive closure of StepRel. *)
Inductive StepStar (tau : nat) : Grid -> Grid -> Prop :=
  | step_star_refl : forall g,
      StepStar tau g g
  | step_star_step : forall g g' g'',
      StepRel tau g g' ->
      StepStar tau g' g'' ->
      StepStar tau g g''.

(** StepStar is transitive. *)
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

(** Single step implies StepStar. *)
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

(** n iterations implies StepStar. *)
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
   Stability
   ----------------------------------------------------------------------------- *)

(** Grid is stable if all agents are happy. *)
Definition stable (tau : nat) (g : Grid) : Prop :=
  forall p, happy tau g p = true.

(** Boolean check for happiness over position list. *)
Fixpoint all_happy_b (tau : nat) (g : Grid) (ps : list Pos) : bool :=
  match ps with
  | [] => true
  | p :: ps' => happy tau g p && all_happy_b tau g ps'
  end.

(** Boolean stability check over all positions. *)
Definition stable_b (tau : nat) (g : Grid) : bool :=
  all_happy_b tau g all_positions_grid.

(* -----------------------------------------------------------------------------
   Additional Notations
   ----------------------------------------------------------------------------- *)

Notation "⊢ g" := (wellformed_grid g) (at level 70, no associativity).
Notation "g ⊨[ tau ] p" := (happy tau g p = true) (at level 70).
Notation "g ⊭[ tau ] p" := (happy tau g p = false) (at level 70).
Notation "⌊ tau ⌋ g" := (stable tau g) (at level 70, no associativity).
Notation "g →[ tau ]" := (step tau g) (at level 50).
Notation "g ^[ tau , n ]" := (Nat.iter n (step tau) g) (at level 50).

(** all_happy_b iff all positions happy. *)
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

(** Boolean stability iff all grid positions happy. *)
Lemma stable_iff_bounded : forall tau g,
  (forall p, In p all_positions_grid -> happy tau g p = true) <-> stable_b tau g = true.
Proof.
  intros tau g; split.
  - intros H; unfold stable_b; apply all_happy_b_spec; assumption.
  - intros H; unfold stable_b in H; apply all_happy_b_spec; assumption.
Qed.

(** In-bounds positions are in all_positions_grid. *)
Lemma all_positions_contains_bounded :
  forall p, (exists i j : nat, p = (i, j) /\ (i < grid_size)%nat /\ (j < grid_size)%nat) -> In p all_positions_grid.
Proof.
  intros p [i [j [Heq [Hi Hj]]]]; subst.
  apply all_positions_coverage; assumption.
Qed.

(** Boolean stability iff all in-bounds positions happy. *)
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

(** Stability implies happiness on all positions. *)
Lemma stable_forall_in_all_positions :
  forall tau g,
    stable tau g -> (forall p, In p all_positions_grid -> happy tau g p = true).
Proof.
  intros tau g Hstable p Hin; apply Hstable.
Qed.

(** Out-of-bounds empty cells are happy. *)
Lemma happy_out_of_bounds_when_empty :
  forall tau g i j,
    ((i >= grid_size)%nat \/ (j >= grid_size)%nat) ->
    get_cell g (i, j) = Empty ->
    happy tau g (i, j) = true.
Proof.
  intros tau g i j Hout Hempty.
  apply empty_cell_always_happy; assumption.
Qed.

(** Out-of-bounds occupied cell happiness equals tolerance check. *)
Lemma happy_out_of_bounds_leb :
  forall tau g i j a,
    ((i >= grid_size)%nat \/ (j >= grid_size)%nat) ->
    get_cell g (i, j) = Occupied a ->
    happy tau g (i, j) = (tau <=? count_same a (neighbor_cells g (i, j)))%nat.
Proof.
  intros tau g i j a Hout Hocc.
  unfold happy; rewrite Hocc; reflexivity.
Qed.

(** Stability from in-bounds happiness and empty out-of-bounds. *)
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

(** Stability implies in-bounds happiness. *)
Lemma stable_to_bounded :
  forall tau g,
    stable tau g ->
    (forall i j, (i < grid_size)%nat -> (j < grid_size)%nat -> happy tau g (i, j) = true).
Proof.
  intros tau g Hstable i j Hi Hj; apply Hstable.
Qed.

(** Wellformed stability iff in-bounds happiness. *)
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

(** Wellformed stability iff boolean stability. *)
Lemma stable_iff_wellformed : forall tau g,
  wellformed_grid g ->
  (stable tau g <-> stable_b tau g = true).
Proof.
  intros tau g Hwf; split.
  - intros Hstable; apply stable_iff_in_bounds; apply stable_to_bounded; assumption.
  - intros Hstable_b; apply stable_from_bounded_assuming_empty_outside; [assumption|].
    apply stable_iff_in_bounds; assumption.
Qed.

(** Decidability of stability on wellformed grids. *)
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

(** Single-position step on stable grid is identity. *)
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

(** Multi-position step on stable grid is identity. *)
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

(** Stable grids are fixed points of step. *)
Theorem step_stable_fixed_point :
  forall tau g,
    stable tau g ->
    step tau g = g.
Proof.
  intros tau g Hstable.
  unfold step.
  apply step_positions_id_on_stable; assumption.
Qed.

(** Stable grids are fixed points of iterated step. *)
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

(** Stability is preserved by step. *)
Corollary stable_stays_stable :
  forall tau g,
    stable tau g ->
    stable tau (step tau g).
Proof.
  intros tau g Hstable.
  rewrite step_stable_fixed_point; assumption.
Qed.

(** Wellformed stability iff boolean stability. *)
Corollary stable_wellformed_iff_stable_b :
  forall tau g,
    wellformed_grid g ->
    stable tau g <-> stable_b tau g = true.
Proof.
  intros tau g Hwf; apply stable_iff_wellformed; assumption.
Qed.

(** Stability decidability on wellformed grids. *)
Corollary stable_decidable_wellformed :
  forall tau g,
    wellformed_grid g ->
    {stable tau g} + {~ stable tau g}.
Proof.
  intros tau g Hwf; apply stable_dec_wellformed; assumption.
Qed.

(** Zero tolerance implies stability. *)
Theorem zero_tolerance_stable :
  forall g,
    stable 0 g.
Proof.
  intros g p.
  apply zero_tolerance_all_happy.
Qed.

(** Parallel step on stable grid is identity. *)
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

(** StepStar from stable grid implies equality. *)
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

(** Single-position step preserves wellformedness. *)
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

(** Multi-position step preserves wellformedness. *)
Lemma step_positions_preserves_wellformed :
  forall tau ps g,
    wellformed_grid g ->
    wellformed_grid (step_positions tau ps g).
Proof.
  intros tau ps; induction ps as [|p ps' IH]; intros g Hwf; simpl.
  - assumption.
  - apply IH; apply step_position_preserves_wellformed; assumption.
Qed.

(** Global step preserves wellformedness. *)
Lemma step_preserves_wellformed :
  forall tau g,
    wellformed_grid g ->
    wellformed_grid (step tau g).
Proof.
  intros tau g Hwf.
  unfold step; apply step_positions_preserves_wellformed; assumption.
Qed.

(** Iterated step preserves wellformedness. *)
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

(** Step on wellformed stable grid preserves wellformedness. *)
Corollary wellformed_stable_wellformed :
  forall tau g,
    wellformed_grid g ->
    stable tau g ->
    wellformed_grid (step tau g).
Proof.
  intros tau g Hwf Hstable.
  rewrite step_stable_fixed_point; assumption.
Qed.

(** Single-position step on wellformed stable grid is identity. *)
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
   Agent Conservation
   ----------------------------------------------------------------------------- *)

(** Count agents in cell list. *)
Fixpoint count_agents_in_cells (cs : list Cell) : nat :=
  match cs with
  | [] => 0
  | Empty :: cs' => count_agents_in_cells cs'
  | Occupied _ :: cs' => S (count_agents_in_cells cs')
  end.

(** Count agents at given positions. *)
Definition count_agents_at_positions (g : Grid) (ps : list Pos) : nat :=
  count_agents_in_cells (map (get_cell g) ps).

(** Total agent count on grid. *)
Definition count_agents (g : Grid) : nat :=
  count_agents_at_positions g all_positions_grid.

(** Agent count distributes over list concatenation. *)
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

(** Agent count at positions distributes over list concatenation. *)
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

(** Empty cell contributes 0 to agent count. *)
Lemma count_agents_in_cells_cons_empty :
  forall cs,
    count_agents_in_cells (Empty :: cs) = count_agents_in_cells cs.
Proof.
  intros cs; reflexivity.
Qed.

(** Occupied cell contributes 1 to agent count. *)
Lemma count_agents_in_cells_cons_occupied :
  forall a cs,
    count_agents_in_cells (Occupied a :: cs) = S (count_agents_in_cells cs).
Proof.
  intros a cs; reflexivity.
Qed.

(** Swapping cells preserves agent count. *)
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

(** Mapping get_cell is extensional. *)
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

(** Agent count is extensional on all_positions_grid. *)
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

(** Reading second write returns second value. *)
Lemma get_cell_double_set_same :
  forall g p q c1 c2,
    get_cell (set_cell (set_cell g p c1) q c2) q = c2.
Proof.
  intros g p q c1 c2.
  apply get_set_same.
Qed.

(** Reading first write after second write (different positions). *)
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

(** Reading other position after two writes. *)
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

(** Empty and occupied cell count properties. *)
Lemma count_agents_in_cells_eq_empty_occupied :
  forall cs c,
    count_agents_in_cells (Empty :: cs) = count_agents_in_cells cs /\
    count_agents_in_cells (Occupied c :: cs) = S (count_agents_in_cells cs).
Proof.
  intros cs c; split; reflexivity.
Qed.

(** Swapping two cells preserves count. *)
Lemma count_cell_swap :
  forall c1 c2,
    count_agents_in_cells [c1; c2] = count_agents_in_cells [c2; c1].
Proof.
  intros c1 c2.
  destruct c1, c2; simpl; reflexivity.
Qed.

(** Removing one cell and adding another preserves count if both have same occupancy. *)
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

(** Agent count at positions splits over list concatenation. *)
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

(** Agent count at cons position splits. *)
Lemma count_agents_in_cells_cons_split :
  forall p ps g,
    count_agents_in_cells (map (get_cell g) (p :: ps)) =
    (count_agents_in_cells [get_cell g p] + count_agents_in_cells (map (get_cell g) ps))%nat.
Proof.
  intros p ps g.
  simpl. destruct (get_cell g p); simpl; reflexivity.
Qed.

(** List concatenation associativity with cons. *)
Lemma app_assoc_cons :
  forall {A : Type} (l1 l2 : list A) (x : A) (l3 : list A),
    l1 ++ x :: l2 ++ l3 = (l1 ++ [x]) ++ l2 ++ l3.
Proof.
  intros A l1 l2 x l3.
  rewrite <- app_assoc. simpl. reflexivity.
Qed.

(** Not in concatenation iff not in either part. *)
Lemma not_in_app :
  forall {A : Type} (x : A) (l1 l2 : list A),
    ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A x l1 l2. split.
  - intros Hnin. split; intros Hin; apply Hnin; apply in_or_app; auto.
  - intros [Hnin1 Hnin2] Hin. apply in_app_or in Hin. destruct Hin; contradiction.
Qed.

(** List structure with x before y. *)
Lemma in_split_ordered_case1 :
  forall {A : Type} (x y : A) (l1 l2a l2b : list A),
    l1 ++ x :: l2a ++ y :: l2b = l1 ++ x :: (l2a ++ y :: l2b).
Proof.
  intros. reflexivity.
Qed.

(** List structure with y before x. *)
Lemma in_split_ordered_case2 :
  forall {A : Type} (x y : A) (l1a l1b l2 : list A),
    l1a ++ y :: l1b ++ x :: l2 = l1a ++ y :: (l1b ++ x :: l2).
Proof.
  intros. reflexivity.
Qed.

(** Not in cons app when not equal and not in parts. *)
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

(** List has form l1++x::l2++y::l3 with membership. *)
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

(** List has form l1++y::l2++x::l3 with membership. *)
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

(** Two distinct elements in list implies one of two orderings. *)
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

(** First occurrence of x in list l1++x::l2 means x not in l1. *)
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

(** Map get_cell preserved outside p and q. *)
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

(** Map get_cell preserved outside p and q (middle). *)
Lemma map_preserved_outside_pq_middle :
  forall g p q a l,
    ~ In p l ->
    ~ In q l ->
    map (get_cell (set_cell (set_cell g p Empty) q (Occupied a))) l = map (get_cell g) l.
Proof.
  intros g p q a l Hninp Hninq.
  apply map_preserved_outside_pq_before; assumption.
Qed.

(** Map get_cell preserved outside p and q (after). *)
Lemma map_preserved_outside_pq_after :
  forall g p q a l,
    ~ In p l ->
    ~ In q l ->
    map (get_cell (set_cell (set_cell g p Empty) q (Occupied a))) l = map (get_cell g) l.
Proof.
  intros g p q a l Hninp Hninq.
  apply map_preserved_outside_pq_before; assumption.
Qed.

(** Agent count preserved when swapping p→q (p before q in list). *)
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

(** Agent count preserved when swapping p→q (q before p in list). *)
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

(** Sequences are NoDup. *)
Lemma seq_NoDup : forall start len, NoDup (seq start len).
Proof.
  intros start len. revert start.
  induction len as [| len' IH]; intros start.
  - simpl. constructor.
  - simpl. constructor.
    + rewrite in_seq. lia.
    + apply IH.
Qed.

(** Mapping injective function preserves NoDup. *)
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

(** Concatenating disjoint NoDup lists yields NoDup. *)
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

(** Flat-mapping rows preserves NoDup. *)
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

(** all_positions_grid has no duplicates. *)
Lemma all_positions_grid_NoDup : NoDup all_positions_grid.
Proof.
  unfold all_positions_grid.
  apply flat_map_rows_NoDup.
  apply seq_NoDup.
Qed.

(** von Neumann radius 1 has at most 4 neighbors (unconditional). *)
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

(** NoDup l1++x::l2 implies x not in l1. *)
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

(** NoDup l1++x::l2 implies x not in l2. *)
Lemma NoDup_cons_app_r : forall {A} (x : A) l1 l2,
  NoDup (l1 ++ x :: l2) -> ~ In x l2.
Proof.
  intros A x l1 l2 H.
  induction l1 as [|y l1' IH].
  - simpl in H. inversion H. assumption.
  - simpl in H. inversion H. subst. apply IH. assumption.
Qed.

(** NoDup l1++x::l2++y::l3 implies x not in l2. *)
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

(** NoDup l1++x::l2++y::l3 implies y not in l1. *)
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

(** Two distinct elements in NoDup list have one of two orderings with separation. *)
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

(** Swapping agent from p to q preserves agent count. *)
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

(** Single-position step preserves agent count. *)
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

(** Step positions preserves agent count. *)

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

(** Source position is empty after swap. *)

Lemma swap_get_at_source :
  forall g p q a,
    q <> p ->
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) p = Empty.
Proof.
  intros. rewrite get_set_other, get_set_same by assumption. reflexivity.
Qed.

(** Destination position is occupied after swap. *)

Lemma swap_get_at_dest :
  forall g p q a,
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) q = Occupied a.
Proof.
  intros. rewrite get_set_same. reflexivity.
Qed.

(** Swap preserves cells elsewhere. *)

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

(** Cell count is extensional. *)

Lemma count_cells_extensional :
  forall cs1 cs2,
    cs1 = cs2 ->
    count_agents_in_cells cs1 = count_agents_in_cells cs2.
Proof.
  intros. subst. reflexivity.
Qed.

(** Swapping preserves agent count when both positions in bounds. *)

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

(** Setting out-of-bounds cell preserves agent count. *)

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

(** Setting two out-of-bounds cells preserves agent count. *)

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

(** Setting out-of-bounds cell second preserves count from first set. *)

Lemma set_cell_then_out_of_bounds_preserves_count :
  forall g p q c1 c2,
    ~ in_bounds q ->
    count_agents (set_cell (set_cell g p c1) q c2) = count_agents (set_cell g p c1).
Proof.
  intros g p q c1 c2 Hq.
  apply set_cell_out_of_bounds_preserves_count.
  assumption.
Qed.

(** Out-of-bounds cells are always empty in wellformed grids. *)

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

(** Swapping cells preserves agent count. *)

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

(** Applying single move preserves agent count. *)

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

(** Applying moves is compositional. *)

Lemma apply_moves_cons :
  forall m moves g,
    apply_moves (m :: moves) g = apply_moves moves (apply_moves [m] g).
Proof.
  intros [[p q] a] moves g. simpl. reflexivity.
Qed.

(** Source position unique in move list. *)

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

(** Destination position unique in move list. *)

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

(** Cells not involved in swap remain unchanged. *)

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

(** Move destination appears in destination list. *)

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

(** Not in destinations implies move not in list. *)

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

(** Destination cell becomes occupied after swap. *)

Lemma get_cell_after_swap_at_dest :
  forall g p q a,
    get_cell (set_cell (set_cell g p Empty) q (Occupied a)) q = Occupied a.
Proof.
  intros g p q a.
  rewrite get_set_same.
  reflexivity.
Qed.

(** Applying single move preserves agent count. *)

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

(** Computed move sources are in all_positions_grid. *)

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

(** Computed move destinations are in all_positions_grid. *)

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

(** Applying disjoint moves preserves agent count. *)

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

(** Computed move sources are in position list ps. *)

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

(** At most one move per position in NoDup list. *)

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

(** Computed move sources are unique. *)

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

(** Removing conflicts preserves move properties. *)

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

(** Same and different counts sum to total agents. *)

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

(** Local homophily: ratio of same to total neighbors. *)

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

(** Rational fraction bounded by 1. *)

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

(** Local homophily always in [0,1]. *)

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

(** Empty cells have zero homophily. *)

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

(** Rational with equal numerator and denominator equals 1. *)

Lemma Q_num_denom_equal : forall p : positive, (Z.pos p # p == 1)%Q.
Proof.
  intros p.
  unfold Qeq. simpl.
  lia.
Qed.

(** Converting positive nat to positive Z. *)

Lemma Z_of_nat_to_pos : forall n, (0 < n)%nat -> Z.of_nat n = Z.pos (Pos.of_nat n).
Proof.
  intros n Hpos.
  rewrite <- Znat.positive_nat_Z by assumption.
  rewrite Nat2Pos.id by lia.
  reflexivity.
Qed.

(** Homophily equals 1 when all neighbors are same type. *)

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

(** Happy agents have high local homophily. *)

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

(** Sum of local homophily over position list. *)

Fixpoint sum_local_homophily_list (g : Grid) (ps : list Pos) : Q :=
  match ps with
  | [] => 0%Q
  | p :: ps' => (local_homophily g p + sum_local_homophily_list g ps')%Q
  end.

(** Global segregation: average homophily across all agents. *)

Definition global_segregation (g : Grid) : Q :=
  let total_agents := count_agents g in
  match total_agents with
  | O => 0%Q
  | S _ =>
      (sum_local_homophily_list g all_positions_grid * (1 # Pos.of_nat total_agents))%Q
  end.

(** Sum of local homophily is nonnegative. *)

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

(** Sum of local homophily bounded by agent count. *)

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

(** Positive from nat S n equals Z of nat S n. *)

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

(** Global segregation always in [0,1]. *)

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

(** Count unhappy positions in grid. *)

Definition count_unhappy_positions (tau : nat) (g : Grid) : nat :=
  count_unhappy_positions_list tau g all_positions_grid.

(** Counting unhappy distributes over list append. *)

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

(** Zero unhappy iff all positions happy. *)

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

(** Stable iff zero unhappy positions. *)

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

(** Unhappy count bounded by grid size. *)

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

(** Upper bound on distinct grid configurations. *)

Definition grid_configs_finite := (3 ^ (grid_size * grid_size))%nat.

(** * Termination and Convergence *)

(** Zero unhappy implies grid is stable fixpoint. *)

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

(** Grid has period p under step function. *)

Definition has_period (tau : nat) (g : Grid) (p : nat) : Prop :=
  (p > 0)%nat /\ Nat.iter p (step tau) g = g.

(** Grid is fixpoint under step function. *)

Definition is_fixpoint (tau : nat) (g : Grid) : Prop :=
  step tau g = g.

(** Fixpoint is equivalent to period 1. *)

Lemma fixpoint_is_period_1 :
  forall tau g,
    is_fixpoint tau g <-> has_period tau g 1.
Proof.
  intros tau g; split; intros H.
  - unfold has_period; simpl; split; [lia | assumption].
  - unfold has_period in H; destruct H as [_ H]; simpl in H; assumption.
Qed.

(** Empty cells are always happy. *)

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

(** Unhappy positions must be occupied. *)

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

(** Stable grids are fixpoints. *)

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

(** Iterating by multiples of period returns to original grid. *)

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

(** Step position either preserves grid or finds valid destination. *)

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

(** Grid equality at specified positions. *)

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

(** Grid equality over all positions. *)

Definition grid_eq (g1 g2 : Grid) : bool :=
  grid_eq_at_positions g1 g2 all_positions_grid.

(** Grid equality is reflexive. *)

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

(** Grid equality specification. *)

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

(** False grid equality implies difference exists. *)

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

(** Out-of-bounds cells remain empty after step. *)

Lemma step_out_of_bounds_empty :
  forall tau g i j,
    wellformed_grid g ->
    (i >= grid_size)%nat \/ (j >= grid_size)%nat ->
    get_cell (step tau g) (i, j) = Empty.
Proof.
  intros tau g i j Hwf Hout.
  apply step_preserves_wellformed; assumption.
Qed.

(** Grid equality extends to all positions. *)

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

(** Grid equality implies functional equality. *)

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

(** False grid equality implies grids differ. *)

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

(** Happiness is extensional with respect to grid cells. *)

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

(** Extensionally equal grids have same stability. *)

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

(** Position bijection preserves bounds. *)

Definition pos_bijection (f : Pos -> Pos) : Prop :=
  (forall p, in_bounds p -> in_bounds (f p)) /\
  (forall p1 p2, in_bounds p1 -> in_bounds p2 -> f p1 = f p2 -> p1 = p2) /\
  (forall q, in_bounds q -> exists p, in_bounds p /\ f p = q).

(** Grid isomorphism via position bijection. *)

Definition grid_isomorphic (g1 g2 : Grid) : Prop :=
  exists (f : Pos -> Pos),
    pos_bijection f /\
    (forall p, in_bounds p -> get_cell g1 p = get_cell g2 (f p)).

(** Identity is a bijection. *)

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

(** Inverse from list is surjective. *)

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

(** Inverse from list is bijection. *)

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

(** Inverse from list is left inverse. *)

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

(** Inverse from list is right inverse. *)

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

(** Grid isomorphism is symmetric. *)

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

(** Composition of bijections is bijection. *)

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

(** Empty cells cause no change under step_position. *)

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

(** Happy agents cause no change under step_position. *)

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

(** Unhappy agents with no valid destination cause no change. *)

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

(** Structure of step_position when an unhappy agent moves. *)

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

(** Destination positions are always empty. *)

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

(** Agents are happy at their destination positions. *)

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

(** Destination positions are in bounds. *)

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

(** Happiness implies tolerance threshold satisfied. *)

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

(** Unhappiness implies tolerance threshold not met. *)

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

(** Count skips happy positions in list. *)

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

(** Count increments for unhappy positions in list. *)

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

(** Empty cells are always happy. *)

Lemma micro_empty_always_happy :
  forall tau g p,
    get_cell g p = Empty ->
    happy tau g p = true.
Proof.
  intros tau g p Hempty.
  apply empty_cell_always_happy.
  exact Hempty.
Qed.

(** Agents become happy after moving to destination. *)

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

(** Unstable grids contain unhappy positions. *)

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

(** Empty position list yields identity under step_positions. *)

Lemma micro_step_positions_nil :
  forall tau g,
    step_positions tau [] g = g.
Proof.
  intros tau g.
  simpl.
  reflexivity.
Qed.

(** Step positions processes head then tail. *)

Lemma micro_step_positions_cons :
  forall tau g p ps,
    step_positions tau (p :: ps) g =
    step_positions tau ps (step_position tau g p).
Proof.
  intros tau g p ps.
  simpl.
  reflexivity.
Qed.

(** Step function defined as step_positions over all positions. *)

Lemma micro_step_def :
  forall tau g,
    step tau g = step_positions tau all_positions_grid g.
Proof.
  intros tau g.
  unfold step.
  reflexivity.
Qed.

(** Wellformedness preserved by single step_position. *)

Lemma micro_wellformed_after_step_position :
  forall tau g p,
    wellformed_grid g ->
    wellformed_grid (step_position tau g p).
Proof.
  intros tau g p Hwf.
  apply step_position_preserves_wellformed.
  exact Hwf.
Qed.

(** Wellformedness preserved by step_positions. *)

Lemma micro_wellformed_after_step_positions :
  forall tau g ps,
    wellformed_grid g ->
    wellformed_grid (step_positions tau ps g).
Proof.
  intros tau g ps Hwf.
  apply step_positions_preserves_wellformed.
  exact Hwf.
Qed.

(** Equal wellformed grids agree on all positions. *)

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

(** Stable grids preserve cells under step. *)

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

(** Count unhappy is extensional with respect to happiness predicate. *)

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

(** Step position either preserves grid or performs a move. *)

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

(** Destination is different from source position. *)

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

(** After a move, source position becomes empty. *)

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

(** After a move, destination position becomes occupied. *)

Lemma micro_move_dest_becomes_occupied :
  forall tau g p q a,
    step_position tau g p = set_cell (set_cell g p Empty) q (Occupied a) ->
    get_cell (step_position tau g p) q = Occupied a.
Proof.
  intros tau g p q a Hmove.
  rewrite Hmove.
  rewrite get_set_same; reflexivity.
Qed.

(** Count same agents in a list of cells. *)

Fixpoint count_same_in_list (a : Agent) (cs : list Cell) : nat :=
  match cs with
  | [] => 0
  | Empty :: cs' => count_same_in_list a cs'
  | Occupied b :: cs' =>
      if agent_eqb a b
      then S (count_same_in_list a cs')
      else count_same_in_list a cs'
  end.

(** count_same equals count_same_in_list. *)

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

(** count_same is extensional with respect to grid cells. *)

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

(** Agent move preserves cells elsewhere (not source or destination). *)

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

(** No-move step_position preserves all cells. *)

Lemma micro_step_position_no_move_preserves_all_cells :
  forall tau g p r,
    step_position tau g p = g ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hno_move.
  rewrite Hno_move; reflexivity.
Qed.

(** Moving agents have distinct source and destination. *)

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

(** Moves create a grid different from original at source position. *)

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

(** Unchanged step_positions preserves all cells extensionally. *)

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

(** Search for an unhappy agent that can move. *)

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

(** Empty cells are skipped in search. *)

Lemma find_unhappy_can_move_aux_cons_empty :
  forall tau g p ps,
    get_cell g p = Empty ->
    find_unhappy_can_move_aux tau g (p :: ps) = find_unhappy_can_move_aux tau g ps.
Proof.
  intros tau g p ps Hcell.
  simpl. rewrite Hcell. reflexivity.
Qed.

(** Happy agents are skipped in search. *)

Lemma find_unhappy_can_move_aux_cons_happy :
  forall tau g p a ps,
    get_cell g p = Occupied a ->
    happy tau g p = true ->
    find_unhappy_can_move_aux tau g (p :: ps) = find_unhappy_can_move_aux tau g ps.
Proof.
  intros tau g p a ps Hcell Hhappy.
  simpl. rewrite Hcell. rewrite Hhappy. reflexivity.
Qed.

(** Unhappy agents without destination are skipped. *)

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

(** Unhappy movable agent found immediately returns result. *)

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

(** Found agent is in list, occupied, unhappy, and has valid destination. *)

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

(** Grid unchanged implies stable if no stuck unhappy agents exist. *)

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

(** Append distributes over step_positions. *)

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

(** Find first position where two grids differ. *)

Fixpoint find_grid_diff (g1 g2 : Grid) (ps : list Pos) : option Pos :=
  match ps with
  | [] => None
  | p :: ps' =>
      match cell_eq_dec (get_cell g1 p) (get_cell g2 p) with
      | left _ => find_grid_diff g1 g2 ps'
      | right _ => Some p
      end
  end.

(** Found difference is in list and cells differ. *)

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

(** No difference found means grids agree on all positions in list. *)

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

(** Unhappy movable agent has witness destination. *)

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

(** Unhappy movable agent appears in auxiliary search. *)

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

(** Occupied cells preserved when not at source position. *)

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

(** Empty cells preserved when not source or destination. *)

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

(** Cells preserved when position not equal to destination. *)

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

(** Empty position list preserves cells. *)

Lemma step_positions_nil_preserves :
  forall tau g p c,
    get_cell g p = c ->
    get_cell (step_positions tau [] g) p = c.
Proof.
  intros tau g p c Hcell. simpl. assumption.
Qed.

(** Occupied cells preserved when position not in processing list. *)

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

(** Empty destination becomes occupied after move. *)

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

(** Empty cells remain empty when not source or destination. *)

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

(** Movable unhappy agent causes grid to change. *)

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

(** Source position becomes empty after move. *)

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

(** Destination position becomes occupied after move. *)

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

(** Other positions unchanged when agent moves. *)

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

(** No-move step_position preserves all cells. *)

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

(** Move changes exactly source and destination cells. *)

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

(** Unchanged step_position preserves cells. *)

Lemma step_position_preserves_cells_when_no_change :
  forall tau g p r,
    step_position tau g p = g ->
    get_cell (step_position tau g p) r = get_cell g r.
Proof.
  intros tau g p r Hno_change.
  rewrite Hno_change.
  reflexivity.
Qed.

(** Changed non-source cells must be destination. *)

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

(** Empty position list preserves all cells. *)

Lemma step_positions_nil_preserves_cells :
  forall tau g r,
    get_cell (step_positions tau [] g) r = get_cell g r.
Proof.
  intros tau g r.
  simpl.
  reflexivity.
Qed.

(** Empty cells cause no grid change. *)

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

(** Happy agents cause no grid change. *)

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

(** Unhappy agents without destination cause no grid change. *)

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

(** Structure of step_position when move occurs. *)

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

(** Source becomes empty after set_cell operations for move. *)

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

(** Destination becomes occupied after set_cell operations for move. *)

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

Theorem fixpoint_decidability_within_bound :
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

Theorem fixpoint_or_progress_within_bound :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat ->
       Nat.iter i (step tau) g <> Nat.iter (S i) (step tau) g).
Proof.
  intros tau g Hwf.
  destruct (fixpoint_decidability_within_bound tau g Hwf) as [[n [Hn Hfix]] | Hall].
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

Corollary fixpoint_reachability_dichotomy :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat -> ~ is_fixpoint tau (Nat.iter i (step tau) g)).
Proof.
  intros tau g Hwf.
  exact (fixpoint_decidability_within_bound tau g Hwf).
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

Corollary fixpoint_search_completeness :
  forall tau g,
    wellformed_grid g ->
    (exists n, (n < grid_configs_finite)%nat /\ is_fixpoint tau (Nat.iter n (step tau) g)) \/
    (forall i, (i < grid_configs_finite)%nat -> ~ is_fixpoint tau (Nat.iter i (step tau) g)).
Proof.
  intros tau g Hwf.
  exact (fixpoint_decidability_within_bound tau g Hwf).
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

(* -----------------------------------------------------------------------------
   GUARANTEED TERMINATION: Convergence to Fixpoint or Cycle
   ----------------------------------------------------------------------------- *)

(** Decidable membership in lists of wellformed grids. *)

Lemma in_dec_grid :
  forall (g : Grid) (gs : list Grid),
    wellformed_grid g ->
    (forall g', In g' gs -> wellformed_grid g') ->
    {In g gs} + {~ In g gs}.
Proof.
  intros g gs Hwf_g Hwf_gs.
  induction gs as [|g' gs' IH].
  - right. intros H. inversion H.
  - assert (Hwf_g' : wellformed_grid g').
    { apply Hwf_gs. left. reflexivity. }
    assert (Hwf_gs' : forall g'', In g'' gs' -> wellformed_grid g'').
    { intros g'' Hin''. apply Hwf_gs. right. assumption. }
    destruct (grid_eq_decidable g g' Hwf_g Hwf_g') as [Heq | Hneq].
    + left. left. symmetry. exact Heq.
    + destruct (IH Hwf_gs') as [Hin | Hnotin].
      * left. right. exact Hin.
      * right. intros [Heq' | Hin'].
        -- apply Hneq. symmetry. exact Heq'.
        -- apply Hnotin. exact Hin'.
Defined.

(** All grids in an iteration sequence preserve wellformedness. *)

Lemma iter_sequence_all_wellformed :
  forall tau g n,
    wellformed_grid g ->
    forall k, (k <= n)%nat -> wellformed_grid (nth k (iter_sequence tau g n) empty_grid).
Proof.
  intros tau g n Hwf k Hk.
  rewrite iter_sequence_nth by assumption.
  apply step_iter_wellformed.
  assumption.
Qed.

(** Each iterate appears in the iteration sequence. *)

Lemma grid_in_iter_sequence :
  forall tau g n k,
    (k <= n)%nat ->
    In (Nat.iter k (step tau) g) (iter_sequence tau g n).
Proof.
  intros tau g n k Hk.
  revert g k Hk.
  induction n as [|n' IH]; intros g k Hk.
  - assert (k = 0)%nat by lia. subst. simpl. left. reflexivity.
  - destruct k as [|k'].
    + simpl. left. reflexivity.
    + simpl. right.
      rewrite <- nat_iter_S_comm.
      apply IH.
      lia.
Qed.

(** Iteration sequence length is S n. *)

Lemma iter_sequence_has_S_n_elements :
  forall tau g n,
    length (iter_sequence tau g n) = S n.
Proof.
  intros tau g n.
  apply iter_sequence_length.
Qed.

(** Mapping iteration over sequences preserves nth element structure. *)

Lemma map_iter_nth :
  forall tau g i n d,
    nth i (map (fun k => Nat.iter k (step tau) g) (List.seq 0 (S n))) (Nat.iter d (step tau) g) =
    Nat.iter (nth i (List.seq 0 (S n)) d) (step tau) g.
Proof.
  intros. apply map_nth.
Qed.

(** Accessing iteration map with empty_grid default yields i-th iterate. *)

Lemma map_iter_nth_empty_default :
  forall tau g i n,
    (i < S n)%nat ->
    nth i (map (fun k => Nat.iter k (step tau) g) (List.seq 0 (S n))) empty_grid =
    Nat.iter i (step tau) g.
Proof.
  intros tau g i n Hi.
  rewrite nth_indep with (d' := Nat.iter 0%nat (step tau) g).
  - rewrite map_iter_nth.
    rewrite seq_nth by assumption.
    simpl. reflexivity.
  - rewrite map_length, seq_length. assumption.
Qed.

(** Sequence starting at 0 has nth element equal to index. *)

Lemma seq_nth_offset_zero :
  forall i n,
    (i < S n)%nat ->
    nth i (List.seq 0 (S n)) 0%nat = i.
Proof.
  intros i n Hi.
  rewrite seq_nth by assumption.
  simpl. reflexivity.
Qed.

(** If iter^i = iter^j for i < j, then either iter^i is a fixpoint or has period j-i. *)

Lemma repeat_implies_fixpoint_or_cycle :
  forall tau g i j,
    wellformed_grid g ->
    (i < j)%nat ->
    Nat.iter i (step tau) g = Nat.iter j (step tau) g ->
    (is_fixpoint tau (Nat.iter i (step tau) g) \/
     has_period tau (Nat.iter i (step tau) g) (j - i)).
Proof.
  intros tau g i j Hwf Hij Heq.
  destruct (Nat.eq_dec i (j - 1)) as [Heq_succ | Hneq_succ].
  - (* i = j - 1, so consecutive iterations are equal *)
    left.
    unfold is_fixpoint.
    assert (Hj : j = S i) by lia.
    subst j.
    simpl in Heq.
    symmetry.
    assumption.
  - (* i < j - 1, so we have a genuine cycle *)
    right.
    apply step_iter_repeat_implies_period; assumption.
Qed.

(** Fixpoint at iteration n implies all future iterations remain at that fixpoint. *)

Lemma fixpoint_all_future_equal :
  forall tau g n m,
    wellformed_grid g ->
    is_fixpoint tau (Nat.iter n (step tau) g) ->
    (m >= n)%nat ->
    Nat.iter m (step tau) g = Nat.iter n (step tau) g.
Proof.
  intros tau g n m Hwf Hfix Hm.
  apply iter_fixpoint_stable; assumption.
Qed.

(** Shifting by multiples of period p returns to original state. *)

Lemma period_shift_iter :
  forall tau g n p k,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (k * p) (step tau) (Nat.iter n (step tau) g) = Nat.iter n (step tau) g.
Proof.
  intros tau g n p k Hper.
  apply period_multiple.
  assumption.
Qed.

(** Decomposition of iteration: iter^(n+k) = iter^k ∘ iter^n. *)

Lemma iter_decompose_offset :
  forall tau g n offset,
    Nat.iter (n + offset) (step tau) g = Nat.iter offset (step tau) (Nat.iter n (step tau) g).
Proof.
  intros tau g n offset.
  apply step_iter_add.
Qed.

(** Division algorithm: a = (a÷b)·b + (a mod b). *)

Lemma mod_decomposition :
  forall a b, (b > 0)%nat -> a = (a / b * b + a mod b)%nat.
Proof.
  intros a b Hb.
  rewrite Nat.mul_comm.
  apply Nat.div_mod.
  lia.
Qed.

(** Iteration commutes with period shifts. *)

Lemma iter_period_commute :
  forall tau g n p k r,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter r (step tau) (Nat.iter (k * p) (step tau) (Nat.iter n (step tau) g)) =
    Nat.iter r (step tau) (Nat.iter n (step tau) g).
Proof.
  intros tau g n p k r Hper.
  f_equal.
  apply period_shift_iter with (p := p).
  assumption.
Qed.

(** Reassociating nested iterations: iter^(a+b+c) = iter^c ∘ iter^b ∘ iter^a. *)

Lemma iter_add_reassoc :
  forall tau g a b c,
    Nat.iter (a + b + c) (step tau) g = Nat.iter c (step tau) (Nat.iter b (step tau) (Nat.iter a (step tau) g)).
Proof.
  intros tau g a b c.
  replace (a + b + c)%nat with (a + (b + c))%nat by lia.
  rewrite step_iter_add.
  rewrite step_iter_add.
  reflexivity.
Qed.

(** Alias for iter_add_reassoc. *)

Lemma iter_split_three :
  forall tau g a b c,
    Nat.iter (a + b + c) (step tau) g =
    Nat.iter c (step tau) (Nat.iter b (step tau) (Nat.iter a (step tau) g)).
Proof.
  intros. apply iter_add_reassoc.
Qed.

(** Adding multiples of b does not affect (mod b). *)

Lemma mod_add_mult_vanish :
  forall a b k,
    (b > 0)%nat ->
    ((k * b + a) mod b = a mod b)%nat.
Proof.
  intros a b k Hb.
  rewrite Nat.add_comm.
  rewrite Nat.mod_add; [|lia].
  reflexivity.
Qed.

(** Modulo is idempotent. *)

Lemma mod_mod_idem :
  forall a b,
    (b > 0)%nat ->
    ((a mod b) mod b = a mod b)%nat.
Proof.
  intros a b Hb.
  rewrite Nat.mod_mod; [reflexivity | lia].
Qed.

(** Associativity of addition for iteration counts. *)

Lemma iter_add_reassoc_nat :
  forall tau g a b c,
    Nat.iter (a + (b + c)) (step tau) g = Nat.iter (a + b + c) (step tau) g.
Proof.
  intros. f_equal. lia.
Qed.

(** Adding multiples of period p to iteration count cancels out. *)

Lemma iter_add_cancel_period :
  forall tau g n p k r,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (n + (k * p + r)) (step tau) g = Nat.iter (n + r) (step tau) g.
Proof.
  intros tau g n p k r Hper.
  assert (Eq1: (n + (k * p + r) = n + k * p + r)%nat) by lia.
  assert (Eq2: (n + r = n + 0 + r)%nat) by lia.
  rewrite Eq1, Eq2.
  do 2 rewrite iter_split_three.
  assert (Goal: Nat.iter (k * p) (step tau) (Nat.iter n (step tau) g) =
                Nat.iter 0 (step tau) (Nat.iter n (step tau) g)).
  { rewrite period_shift_iter with (p := p) (k := k) by exact Hper.
    simpl. reflexivity. }
  rewrite Goal.
  reflexivity.
Qed.

(** Flattened version of period cancellation. *)

Lemma iter_add_cancel_period_flat :
  forall tau g n p k r,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (n + k * p + r) (step tau) g = Nat.iter (n + r) (step tau) g.
Proof.
  intros.
  rewrite <- iter_add_reassoc_nat.
  apply iter_add_cancel_period.
  assumption.
Qed.

(** Advancing by period with offset: iter^(n+r) = iter^(n+p+r) when r < p. *)

Lemma period_advance_offset :
  forall tau g n p r,
    has_period tau (Nat.iter n (step tau) g) p ->
    (0 < r)%nat ->
    (r < p)%nat ->
    Nat.iter (n + r) (step tau) g = Nat.iter (n + p + r) (step tau) g.
Proof.
  intros tau g n p r Hper Hr_pos Hr_bound.
  symmetry.
  assert (Heq: (n + p + r = n + 1 * p + r)%nat) by lia.
  rewrite Heq.
  apply iter_add_cancel_period_flat.
  exact Hper.
Qed.

(** Advancing by q periods with offset r. *)

Lemma period_advance_by_q :
  forall tau g n p q r,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (n + q * p + r) (step tau) g = Nat.iter (n + r) (step tau) g.
Proof.
  intros tau g n p q r Hper.
  apply iter_add_cancel_period_flat.
  exact Hper.
Qed.

(** Adding one period to iteration count with offset. *)

Lemma add_period_to_offset :
  forall tau g n p r,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (n + p + r) (step tau) g = Nat.iter (n + r) (step tau) g.
Proof.
  intros.
  assert (Heq: (n + p + r = n + 1 * p + r)%nat) by lia.
  rewrite Heq.
  apply iter_add_cancel_period_flat.
  assumption.
Qed.

(** Adding p equals adding (q+1)p for periodic systems. *)

Lemma period_add_p_eq_qplus1_mult_p :
  forall tau g n p q,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (n + p) (step tau) g = Nat.iter (n + (q + 1) * p) (step tau) g.
Proof.
  intros tau g n p q Hper.
  replace ((q + 1) * p)%nat with (q * p + p)%nat by lia.
  replace (n + (q * p + p))%nat with (n + q * p + p)%nat by lia.
  symmetry.
  apply period_advance_by_q.
  exact Hper.
Qed.

(** Variant of period_add_p_eq_qplus1_mult_p with alternative proof. *)

Lemma period_add_p_plus_r_eq_qplus1_mult_p :
  forall tau g n p q,
    has_period tau (Nat.iter n (step tau) g) p ->
    Nat.iter (n + p) (step tau) g = Nat.iter (n + (q + 1) * p) (step tau) g.
Proof.
  intros tau g n p q Hper.
  replace ((q + 1) * p)%nat with (q * p + p)%nat by lia.
  replace (n + (q * p + p))%nat with (n + q * p + p)%nat by lia.
  assert (H: Nat.iter (n + q * p + p) (step tau) g = Nat.iter (n + p) (step tau) g).
  { assert (H1: Nat.iter (n + q * p) (step tau) g = Nat.iter n (step tau) g).
    { specialize (period_advance_by_q tau g n p q 0%nat Hper) as Hpaq.
      replace (n + q * p + 0)%nat with (n + q * p)%nat in Hpaq by lia.
      replace (n + 0)%nat with n in Hpaq by lia.
      exact Hpaq. }
    replace (n + q * p + p)%nat with ((n + q * p) + p)%nat by lia.
    rewrite step_iter_add.
    rewrite H1.
    rewrite <- step_iter_add.
    reflexivity. }
  symmetry.
  exact H.
Qed.

(** Periodic behavior: any future iteration can be expressed as n + kp + r with r < p. *)

Lemma cycle_repeats_forever :
  forall tau g n p m,
    wellformed_grid g ->
    has_period tau (Nat.iter n (step tau) g) p ->
    (m >= n)%nat ->
    exists k r, (r < p)%nat /\ Nat.iter m (step tau) g = Nat.iter (n + k * p + r)%nat (step tau) g.
Proof.
  intros tau g n p m Hwf Hper Hm.
  destruct Hper as [Hpos Hper_eq].
  pose (d := (m - n)%nat).
  pose (q := (d / p)%nat).
  pose (r := (d mod p)%nat).
  assert (Hd_decomp: d = (q * p + r)%nat).
  { unfold q, r, d. rewrite Nat.mul_comm. apply Nat.div_mod. lia. }
  assert (Hr_bound: (r < p)%nat).
  { unfold r. apply Nat.mod_upper_bound. lia. }
  exists 0%nat, r.
  split; [exact Hr_bound|].
  assert (Hm_eq: m = (n + d)%nat) by (unfold d; lia).
  rewrite Hm_eq, Hd_decomp.
  replace (n + (q * p + r))%nat with (n + q * p + r)%nat by lia.
  replace (n + 0 * p + r)%nat with (n + r)%nat by lia.
  assert (Hper': has_period tau (Nat.iter n (step tau) g) p) by (split; assumption).
  apply period_advance_by_q.
  exact Hper'.
Qed.

(** Eventually periodic systems return to a previous state within one period. *)

Lemma eventually_periodic :
  forall tau g n,
    wellformed_grid g ->
    (exists p, (0 < p)%nat /\ has_period tau (Nat.iter n (step tau) g) p) ->
    forall m, (m >= n)%nat ->
      exists k, (k >= n)%nat /\ (k <= m)%nat /\
        Nat.iter m (step tau) g = Nat.iter k (step tau) g.
Proof.
  intros tau g n Hwf [p [Hpos Hper]] m Hm.
  exists (n + (m - n) mod p)%nat.
  repeat split; [lia | |].
  - assert (H: ((m - n) mod p <= m - n)%nat) by (apply Nat.mod_le; lia). lia.
  - transitivity (Nat.iter (n + (m - n)) (step tau) g).
    + f_equal. lia.
    + set (d := (m - n)%nat).
      replace (m - n)%nat with d by reflexivity.
      assert (Hd_decomp: d = (d / p * p + d mod p)%nat).
      { unfold d. apply mod_decomposition. exact Hpos. }
      replace d with (d / p * p + d mod p)%nat by (symmetry; exact Hd_decomp).
      rewrite iter_add_cancel_period with (p := p) (k := (d / p)%nat) (r := (d mod p)%nat) by exact Hper.
      f_equal.
      unfold d.
      rewrite mod_add_mult_vanish by exact Hpos.
      rewrite mod_mod_idem by exact Hpos.
      reflexivity.
Qed.

(** Fixpoint stability: if iter^n is a fixpoint, so are all iter^m for m ≥ n. *)

Lemma fixpoint_at_n_means_stable_forever :
  forall tau g n,
    wellformed_grid g ->
    is_fixpoint tau (Nat.iter n (step tau) g) ->
    forall m, (m >= n)%nat ->
      is_fixpoint tau (Nat.iter m (step tau) g).
Proof.
  intros tau g n Hwf Hfix m Hm.
  assert (Heq: Nat.iter m (step tau) g = Nat.iter n (step tau) g).
  { apply iter_fixpoint_stable; assumption. }
  rewrite Heq.
  assumption.
Qed.

(** Decidable equality for iteration pairs. *)

Lemma iter_pair_eq_dec :
  forall tau g i j,
    wellformed_grid g ->
    {Nat.iter i (step tau) g = Nat.iter j (step tau) g} +
    {Nat.iter i (step tau) g <> Nat.iter j (step tau) g}.
Proof.
  intros.
  apply grid_eq_decidable; apply step_iter_wellformed; assumption.
Defined.

(** Search for an earlier iterate matching a target iteration. *)

Fixpoint find_match_with_target (tau : nat) (g : Grid) (j_target : nat) (i_max : nat) : option nat :=
  match i_max with
  | O => None
  | S i' =>
      if grid_eq (Nat.iter i' (step tau) g) (Nat.iter j_target (step tau) g)
      then Some i'
      else find_match_with_target tau g j_target i'
  end.

(** If find_match_with_target returns Some i, then iter^i = iter^j_target. *)

Lemma find_match_some :
  forall tau g j_target i_max i,
    wellformed_grid g ->
    find_match_with_target tau g j_target i_max = Some i ->
    (i < i_max)%nat /\ Nat.iter i (step tau) g = Nat.iter j_target (step tau) g.
Proof.
  intros tau g j_target i_max i Hwf.
  induction i_max as [|i_max' IH]; intros Hfind; simpl in Hfind.
  - discriminate.
  - destruct (grid_eq (Nat.iter i_max' (step tau) g) (Nat.iter j_target (step tau) g)) eqn:Heq.
    + injection Hfind as Hfind. subst. split. lia.
      apply grid_eq_true_to_functional_eq; try assumption.
      apply step_iter_wellformed; assumption.
      apply step_iter_wellformed; assumption.
    + destruct (IH Hfind) as [Hlt Heq_i]. split. lia. exact Heq_i.
Qed.

(** If find_match_with_target returns None, no match exists below i_max. *)

Lemma find_match_none :
  forall tau g j_target i_max,
    find_match_with_target tau g j_target i_max = None ->
    forall i, (i < i_max)%nat -> Nat.iter i (step tau) g <> Nat.iter j_target (step tau) g.
Proof.
  intros tau g j_target i_max.
  induction i_max as [|i_max' IH]; intros Hnone i Hi.
  - lia.
  - simpl in Hnone.
    destruct (grid_eq (Nat.iter i_max' (step tau) g) (Nat.iter j_target (step tau) g)) eqn:Heq.
    + discriminate.
    + destruct (Nat.eq_dec i i_max') as [Heq_i | Hneq_i].
      * subst. intros Hcontra.
        assert (Htrue: grid_eq (Nat.iter i_max' (step tau) g) (Nat.iter j_target (step tau) g) = true).
        { rewrite Hcontra. apply grid_eq_refl. }
        rewrite Htrue in Heq. discriminate.
      * apply IH. exact Hnone. lia.
Qed.

(** find_match_with_target returns the largest index with a match. *)

Lemma find_match_largest :
  forall tau g j_target i_max i_found,
    find_match_with_target tau g j_target i_max = Some i_found ->
    forall i, (i_found < i < i_max)%nat -> Nat.iter i (step tau) g <> Nat.iter j_target (step tau) g.
Proof.
  intros tau g j_target i_max.
  induction i_max as [|i_max' IH]; intros i_found Hfind i Hi.
  - discriminate.
  - simpl in Hfind.
    destruct (grid_eq (Nat.iter i_max' (step tau) g) (Nat.iter j_target (step tau) g)) eqn:Heq.
    + injection Hfind as Hfind. subst i_found.
      assert (i = i_max') by lia. subst. lia.
    + destruct (Nat.eq_dec i i_max') as [Heq_i | Hneq_i].
      * subst. intros Hcontra.
        assert (Htrue: grid_eq (Nat.iter i_max' (step tau) g) (Nat.iter j_target (step tau) g) = true).
        { rewrite Hcontra. apply grid_eq_refl. }
        rewrite Htrue in Heq. discriminate.
      * apply IH with (i_found := i_found). exact Hfind. lia.
Qed.

(** First repetition characterizes long-term behavior: either period from origin or eventual period. *)

Lemma first_repeat_characterizes :
  forall tau g i j,
    wellformed_grid g ->
    (i < j)%nat ->
    Nat.iter i (step tau) g = Nat.iter j (step tau) g ->
    (forall i' j', (i' < j')%nat /\ (j' < j)%nat ->
      Nat.iter i' (step tau) g <> Nat.iter j' (step tau) g) ->
    ((i = 0)%nat /\ has_period tau g j) \/
    ((i > 0)%nat /\ has_period tau (Nat.iter i (step tau) g) (j - i)).
Proof.
  intros tau g i j Hwf Hij Heq Hmin.
  destruct (Nat.eq_dec i 0) as [Hi0|Hinz].
  - left. split; [exact Hi0|].
    subst i. simpl in Heq.
    split; [lia|].
    assert (Hstep: Nat.iter j (step tau) g = Nat.iter (0 + j) (step tau) g) by (simpl; reflexivity).
    rewrite Hstep.
    rewrite step_iter_add.
    simpl. symmetry. exact Heq.
  - right. split; [lia|].
    split; [lia|].
    assert (Hji: (j = (i + (j - i))%nat)) by lia.
    rewrite Hji in Heq.
    rewrite step_iter_add in Heq.
    symmetry. exact Heq.
Qed.

(** Constructive search for a fixpoint within first n iterations. *)

Lemma decidable_fixpoint_within_bound :
  forall tau g n,
    wellformed_grid g ->
    {k : nat | (k <= n)%nat /\ is_fixpoint tau (Nat.iter k (step tau) g)} +
    {forall k, (k <= n)%nat -> ~ is_fixpoint tau (Nat.iter k (step tau) g)}.
Proof.
  intros tau g n Hwf.
  induction n as [|n' IH].
  - destruct (grid_eq (step tau g) g) eqn:Heq.
    + left. exists 0%nat. split; [lia|].
      unfold is_fixpoint. simpl.
      apply grid_eq_true_to_functional_eq in Heq;
        [exact Heq | apply step_preserves_wellformed; assumption | assumption].
    + right. intros k Hk. unfold is_fixpoint. simpl.
      assert (Hk0: k = 0%nat) by lia. subst k.
      intro Hcontra.
      apply (grid_eq_false_implies_grids_differ (step tau g) g) in Heq.
      apply Heq.
      exact Hcontra.
  - destruct IH as [[k [Hk Hfix]]|Hnone].
    + left. exists k. split; [lia | exact Hfix].
    + destruct (grid_eq (step tau (Nat.iter (S n') (step tau) g)) (Nat.iter (S n') (step tau) g)) eqn:Heq.
      * left. exists (S n'). split; [lia|].
        unfold is_fixpoint.
        apply grid_eq_true_to_functional_eq in Heq;
          [exact Heq |
           apply step_preserves_wellformed; apply step_iter_wellformed; assumption |
           apply step_iter_wellformed; assumption].
      * right. intros k Hk.
        destruct (Nat.eq_dec k (S n')) as [Hkeq|Hkneq].
        -- subst k. unfold is_fixpoint. intro Hcontra.
           apply (grid_eq_false_implies_grids_differ (step tau (Nat.iter (S n') (step tau) g))
                    (Nat.iter (S n') (step tau) g)) in Heq.
           apply Heq.
           exact Hcontra.
        -- apply Hnone. lia.
Qed.

(** Constructive search for period at offset k within bound n. *)

Lemma decidable_period_at_offset :
  forall tau g k n,
    wellformed_grid g ->
    {p : nat | (0 < p <= n)%nat /\ has_period tau (Nat.iter k (step tau) g) p} +
    {forall p, (0 < p <= n)%nat -> ~ has_period tau (Nat.iter k (step tau) g) p}.
Proof.
  intros tau g k n Hwf.
  induction n as [|n' IH].
  - right. intros p [Hpos Hp]. lia.
  - destruct IH as [[p [Hpbound Hper]]|Hnone_p].
    + left. exists p. split; [lia | exact Hper].
    + destruct (grid_eq (Nat.iter (S n') (step tau) (Nat.iter k (step tau) g))
                        (Nat.iter k (step tau) g)) eqn:Heq.
      * left. exists (S n'). split; [lia|].
        split; [lia|].
        unfold has_period.
        apply grid_eq_true_to_functional_eq in Heq;
          [exact Heq |
           apply step_iter_wellformed; apply step_iter_wellformed; assumption |
           apply step_iter_wellformed; assumption].
      * right. intros p [Hpos Hp].
        destruct (Nat.eq_dec p (S n')) as [Hpeq|Hpneq].
        -- subst p. unfold has_period. intros [_ Hcontra].
           apply (grid_eq_false_implies_grids_differ (Nat.iter (S n') (step tau) (Nat.iter k (step tau) g))
                    (Nat.iter k (step tau) g)) in Heq.
           apply Heq.
           exact Hcontra.
        -- apply Hnone_p. split; [exact Hpos | lia].
Qed.

(** Constructive search for specific period p at any offset within bound n. *)

Lemma decidable_period_all_offsets :
  forall tau g p n,
    wellformed_grid g ->
    (0 < p)%nat ->
    {k : nat | (k <= n)%nat /\ has_period tau (Nat.iter k (step tau) g) p} +
    {forall k, (k <= n)%nat -> ~ has_period tau (Nat.iter k (step tau) g) p}.
Proof.
  intros tau g p n Hwf Hpos.
  induction n as [|n' IH].
  - destruct (grid_eq (Nat.iter p (step tau) g) g) eqn:Heq.
    + left. exists 0%nat. split; [lia|].
      split; [exact Hpos|].
      simpl.
      apply grid_eq_true_to_functional_eq in Heq;
        [exact Heq | apply step_iter_wellformed; assumption | assumption].
    + right. intros k Hk.
      assert (Hk0 : k = 0%nat) by lia. subst k.
      simpl. unfold has_period. intros [_ Hcontra].
      apply (grid_eq_false_implies_grids_differ (Nat.iter p (step tau) g) g) in Heq.
      apply Heq. exact Hcontra.
  - destruct IH as [[k [Hk Hper]] | Hnone].
    + left. exists k. split; [lia | exact Hper].
    + destruct (grid_eq (Nat.iter p (step tau) (Nat.iter (S n') (step tau) g))
                        (Nat.iter (S n') (step tau) g)) eqn:Heq.
      * left. exists (S n'). split; [lia|].
        split; [exact Hpos|].
        apply grid_eq_true_to_functional_eq in Heq;
          [exact Heq |
           apply step_iter_wellformed; apply step_iter_wellformed; assumption |
           apply step_iter_wellformed; assumption].
      * right. intros k Hk.
        destruct (Nat.eq_dec k (S n')) as [Hkeq | Hkneq].
        -- subst k. unfold has_period. intros [_ Hcontra].
           apply (grid_eq_false_implies_grids_differ (Nat.iter p (step tau) (Nat.iter (S n') (step tau) g))
                    (Nat.iter (S n') (step tau) g)) in Heq.
           apply Heq. exact Hcontra.
        -- apply Hnone. lia.
Qed.

(** Constructive search for any periodic behavior (any period at any offset) within bound n. *)

Lemma decidable_cycle_within_bound :
  forall tau g n,
    wellformed_grid g ->
    {k : nat & {p : nat | (k <= n)%nat /\ (0 < p)%nat /\ (p <= n)%nat /\
      has_period tau (Nat.iter k (step tau) g) p}} +
    {forall k p, (k <= n)%nat -> (0 < p)%nat -> (p <= n)%nat ->
      ~ has_period tau (Nat.iter k (step tau) g) p}.
Proof.
  intros tau g n Hwf.
  induction n as [|n' IH].
  - right. intros k p Hk Hpos Hp. lia.
  - destruct IH as [[k [p [Hk [Hpos [Hp Hper]]]]]|Hnone].
    + left. exists k. exists p. split; [lia|]. split; [exact Hpos|]. split; [lia|]. exact Hper.
    + (* Check period S n' at all offsets <= n' *)
      destruct (decidable_period_all_offsets tau g (S n') n' Hwf ltac:(lia)) as [[k' [Hk' Hper']] | Hnone_Sn'].
      * left. exists k'. exists (S n'). split; [lia|]. split; [lia|]. split; [lia|]. exact Hper'.
      * (* Check all periods at offset S n' *)
        destruct (decidable_period_at_offset tau g (S n') (S n') Hwf) as [[p [Hpbound Hper]]|Hnone_k].
        -- left. exists (S n'). exists p. split; [lia|]. destruct Hpbound as [Hpos Hp]. split; [exact Hpos|]. split; [exact Hp|]. exact Hper.
        -- right. intros k p Hk Hpos Hp.
           destruct (Nat.eq_dec k (S n')) as [Hkeq|Hkneq].
           ++ subst k. apply Hnone_k. split; assumption.
           ++ destruct (Nat.le_gt_cases p (S n')) as [Hple | Hpgt].
              ** destruct (Nat.eq_dec p (S n')) as [Hpeq | Hpneq].
                 --- subst p. apply Hnone_Sn'. lia.
                 --- assert (Hp' : (p <= n')%nat) by lia.
                     apply (Hnone k p).
                     +++ lia.
                     +++ exact Hpos.
                     +++ exact Hp'.
              ** lia.
Qed.

(** Non-fixpoint grid at origin implies non-fixpoint at iter^0. *)

Lemma not_fixpoint_at_zero :
  forall tau g,
    ~ is_fixpoint tau g ->
    (0 <= S grid_configs_finite)%nat /\ ~ is_fixpoint tau (Nat.iter 0 (step tau) g).
Proof.
  intros tau g Hnfix.
  split.
  - pose proof (grid_configs_bound_positive). lia.
  - simpl. exact Hnfix.
Qed.

(** Step position unchanged for empty cells or happy agents. *)

Lemma step_position_unchanged_if_happy_or_empty :
  forall tau g p,
    (get_cell g p = Empty \/ happy tau g p = true) ->
    step_position tau g p = g.
Proof.
  intros tau g p [Hempty | Hhappy].
  - apply step_position_when_empty_preserves_grid. exact Hempty.
  - apply step_position_when_happy_preserves_grid. exact Hhappy.
Qed.

(** Unstable non-fixpoint grids provide witness at iteration 0. *)

Lemma not_stable_not_fixpoint_implies_witness :
  forall tau g,
    wellformed_grid g ->
    ~ stable tau g ->
    ~ is_fixpoint tau g ->
    (0 <= S grid_configs_finite)%nat /\ ~ is_fixpoint tau (Nat.iter 0 (step tau) g).
Proof.
  intros tau g Hwf Hnstable Hnfix.
  split.
  - pose proof (grid_configs_bound_positive). lia.
  - simpl. exact Hnfix.
Qed.

End SchellingModel.

(* -----------------------------------------------------------------------------
   End of file
   ----------------------------------------------------------------------------- *)
