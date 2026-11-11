module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.ByContra

@[expose] public section

/-! Finite masks and the residual contribution counts in the supplied paper.
Masks describe allowed entries; no nonzero-value premise is imposed. -/

namespace SparseMM

open scoped BigOperators

abbrev Mask (n : ℕ) := Finset (Fin n × Fin n)

def rowMask {n : ℕ} (A : Mask n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i, j) ∈ A

def colMask {n : ℕ} (A : Mask n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i, j) ∈ A

def UniformSparse {n : ℕ} (A : Mask n) (d : ℕ) : Prop :=
  (∀ i, (rowMask A i).card ≤ d) ∧ (∀ j, (colMask A j).card ≤ d)

theorem mask_card_eq_sum_rows {n : ℕ} (A : Mask n) :
    A.card = ∑ i : Fin n, (rowMask A i).card := by
  classical
  simp only [rowMask, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_product']
  simp

theorem mask_card_le {n d : ℕ} (A : Mask n) (hA : UniformSparse A d) :
    A.card ≤ n * d := by
  rw [mask_card_eq_sum_rows]
  calc
    _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => hA.1 i
    _ = _ := by simp

/-- Middle indices contributing to one requested position. -/
def middleSet {n : ℕ} (A B : Mask n) (p : Fin n × Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => (p.1, j) ∈ A ∧ (j, p.2) ∈ B

/-- Potential residual products computed by the processor with middle index j. -/
def residualProducts {n : ℕ} (A B R : Mask n) (j : Fin n) : Mask n :=
  R.filter fun p => (p.1, j) ∈ A ∧ (j, p.2) ∈ B

theorem middleSet_card_le {n d : ℕ} (A B : Mask n)
    (hA : UniformSparse A d) (p : Fin n × Fin n) :
    (middleSet A B p).card ≤ d := by
  apply (Finset.card_le_card (show middleSet A B p ⊆ rowMask A p.1 from ?_)).trans
    (hA.1 p.1)
  intro j hj
  simp only [middleSet, rowMask, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact hj.1

theorem residualProducts_eq_rectangle {n : ℕ} (A B R : Mask n) (j : Fin n) :
    residualProducts A B R j = R ∩ (colMask A j ×ˢ rowMask B j) := by
  ext p
  simp [residualProducts, colMask, rowMask]

/-- The exact double count used for the output-weight bound. -/
theorem residual_contributions_double_count {n : ℕ} (A B R : Mask n) :
    (∑ j : Fin n, (residualProducts A B R j).card) =
      ∑ p ∈ R, (middleSet A B p).card := by
  classical
  simp only [residualProducts, middleSet, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Clustered outputs have zero weight in the residual phase. -/
def residualWeight {n : ℕ} (A B R : Mask n) (p : Fin n × Fin n) : ℕ :=
  if p ∈ R then (middleSet A B p).card else 0

theorem residualWeight_le {n d : ℕ} (A B R : Mask n)
    (hA : UniformSparse A d) (p : Fin n × Fin n) :
    residualWeight A B R p ≤ d := by
  unfold residualWeight
  split_ifs
  · exact middleSet_card_le A B hA p
  · exact Nat.zero_le _

end SparseMM
