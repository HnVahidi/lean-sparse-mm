module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM.Counting

open scoped BigOperators

def load {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (weight : Job → ℕ) (node : Node) : ℕ :=
  ∑ j, if owner j = node then weight j else 0

def count {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (node : Node) : ℕ :=
  (Finset.univ.filter fun j => owner j = node).card

theorem count_eq_load {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (node : Node) :
    count owner node = load owner (fun _ => 1) node := by
  classical
  simp only [count, load, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_load {Job Node : Type*} [Fintype Job] [Fintype Node] [DecidableEq Node]
    (owner : Job → Node) (weight : Job → ℕ) :
    (∑ node, load owner weight node) = ∑ j, weight j := by
  classical
  unfold load
  rw [Finset.sum_comm]
  simp

theorem sum_count {Job Node : Type*} [Fintype Job] [Fintype Node] [DecidableEq Node]
    (owner : Job → Node) : (∑ node, count owner node) = Fintype.card Job := by
  simp_rw [count_eq_load]
  rw [sum_load]
  simp

theorem count_eq_card_fiber {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (node : Node) :
    count owner node = Fintype.card {j // owner j = node} := by
  classical
  simp [count, Fintype.card_subtype]

/-- Count a fiber by injecting its labelled occurrences into a finite set. -/
theorem count_le_card_of_injective {Job Node Target : Type*} [Fintype Job]
    [DecidableEq Node] (owner : Job → Node) (node : Node)
    (s : Finset Target) (f : {j // owner j = node} → {x // x ∈ s})
    (hf : Function.Injective f) : count owner node ≤ s.card := by
  classical
  rw [count_eq_card_fiber]
  simpa using Fintype.card_le_of_injective f hf

theorem count_le_load {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (weight : Job → ℕ) (hw : ∀ j, 0 < weight j) (node : Node) :
    count owner node ≤ load owner weight node := by
  rw [count_eq_load]
  unfold load
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact hw j
  · exact le_rfl

/-- An injective physical placement preserves all per-helper load bounds. -/
theorem load_comp_injective {Job Helper Node : Type*} [Fintype Job]
    [DecidableEq Helper] [DecidableEq Node]
    (owner : Job → Helper) (weight : Job → ℕ) (place : Helper → Node)
    (hplace : Function.Injective place) (B : ℕ)
    (hload : ∀ h, load owner weight h ≤ B) (node : Node) :
    load (place ∘ owner) weight node ≤ B := by
  classical
  by_cases h : ∃ helper, place helper = node
  · obtain ⟨helper, rfl⟩ := h
    have heq : load (place ∘ owner) weight (place helper) = load owner weight helper := by
      unfold load
      apply Finset.sum_congr rfl
      intro j _
      simp [hplace.eq_iff]
    rw [heq]
    exact hload helper
  · have hz : load (place ∘ owner) weight node = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have : place (owner j) ≠ node := fun hj => h ⟨owner j, hj⟩
      simp [this]
    rw [hz]
    exact Nat.zero_le _

end SparseMM.Counting
