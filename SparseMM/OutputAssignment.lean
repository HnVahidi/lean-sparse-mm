module

public import SparseMM.PermutationBalancing
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Simultaneous output-count and contribution-load assignment

Each batch contains one slot per machine. Permuting each batch gives exactly
one slot per machine in that batch; opposing the weight profiles gives the
average-plus-maximum weighted-load bound. Dummy slots have weight zero.
-/

open scoped BigOperators

namespace SparseMM.OutputAssignment

/-- The actual weighted load received by a machine under an assignment. -/
def weightedLoad {Job : Type*} [Fintype Job] {n : ℕ}
    (weights : Job → ℕ) (assignment : Job → Fin n) (i : Fin n) : ℕ :=
  ∑ x : Job, if assignment x = i then weights x else 0

/-- The actual number of assigned slots, independent of their weights. -/
def assignedCount {Job : Type*} [Fintype Job] {n : ℕ}
    (assignment : Job → Fin n) (i : Fin n) : ℕ :=
  ∑ x : Job, if assignment x = i then 1 else 0

theorem sum_perm_fiber {n : ℕ} (p : Equiv.Perm (Fin n))
    (weights : Fin n → ℕ) (i : Fin n) :
    (∑ j : Fin n, if p j = i then weights j else 0) = weights (p.symm i) := by
  classical
  have heq : ∀ j, p j = i ↔ j = p.symm i := by
    intro j
    constructor
    · intro h
      apply p.injective
      simpa only [Equiv.apply_symm_apply] using h
    · intro h
      simp [h]
  simp_rw [heq]
  simp

theorem slot_count {n batches : ℕ}
    (permutations : Fin batches → Equiv.Perm (Fin n)) (i : Fin n) :
    assignedCount (fun x : Fin batches × Fin n => permutations x.1 x.2) i = batches := by
  classical
  unfold assignedCount
  rw [Fintype.sum_prod_type]
  simp_rw [sum_perm_fiber (weights := fun _ => 1)]
  simp

theorem slot_weightedLoad {n batches : ℕ}
    (weights : Fin batches → Fin n → ℕ)
    (permutations : Fin batches → Equiv.Perm (Fin n)) (i : Fin n) :
    weightedLoad (fun x : Fin batches × Fin n => weights x.1 x.2)
      (fun x => permutations x.1 x.2) i = LoadBalancing.assignedLoad weights permutations i := by
  classical
  unfold weightedLoad LoadBalancing.assignedLoad
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun t _ht => sum_perm_fiber (permutations t) (weights t) i

/-- Actual simultaneous assignment on a complete grid of slots: every machine
gets exactly one slot per batch and weighted load at most the average plus one
maximum slot weight (expressed with the averaging denominator cleared). -/
theorem exists_balanced_slot_assignment (n batches W : ℕ)
    (weights : Fin batches → Fin n → ℕ) (hw : ∀ t i, weights t i ≤ W) :
    ∃ assignment : Fin batches × Fin n → Fin n,
      (∀ i : Fin n, assignedCount assignment i = batches) ∧
      ∀ i : Fin n,
        n * weightedLoad (fun x => weights x.1 x.2) assignment i ≤
          (∑ t : Fin batches, ∑ j : Fin n, weights t j) + n * W := by
  obtain ⟨permutations, _hspread, _hsum, hbound⟩ :=
    LoadBalancing.exists_balanced_permutations n batches W weights hw
  refine ⟨fun x => permutations x.1 x.2, fun i => slot_count permutations i, ?_⟩
  intro i
  simpa only [slot_weightedLoad] using hbound i

/-- Extend weights by zero outside an embedding, using singleton fibers. -/
noncomputable def paddedWeight {Job Slot : Type*} [Fintype Job]
    (embedding : Job ↪ Slot) (weights : Job → ℕ) (slot : Slot) : ℕ := by
  classical
  exact ∑ x : Job, if embedding x = slot then weights x else 0

theorem paddedWeight_apply {Job Slot : Type*} [Fintype Job]
    (embedding : Job ↪ Slot) (weights : Job → ℕ) (x : Job) :
    paddedWeight embedding weights (embedding x) = weights x := by
  classical
  unfold paddedWeight
  simp only [embedding.injective.eq_iff]
  simp

theorem paddedWeight_le {Job Slot : Type*} [Fintype Job]
    (embedding : Job ↪ Slot) (weights : Job → ℕ) (W : ℕ)
    (hw : ∀ x, weights x ≤ W) (slot : Slot) :
    paddedWeight embedding weights slot ≤ W := by
  classical
  by_cases h : ∃ x, embedding x = slot
  · obtain ⟨x, rfl⟩ := h
    simpa only [paddedWeight_apply] using hw x
  · have hz : ∀ x, embedding x ≠ slot := fun x hx => h ⟨x, hx⟩
    simp [paddedWeight, hz]

theorem paddedWeight_sum {Job Slot : Type*} [Fintype Job] [Fintype Slot]
    (embedding : Job ↪ Slot) (weights : Job → ℕ) :
    (∑ slot : Slot, paddedWeight embedding weights slot) = ∑ x : Job, weights x := by
  classical
  unfold paddedWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  simp

/-- Summing a nonnegative quantity on embedded jobs costs at most its sum on
all slots. This accounts for deleting dummy outputs. -/
theorem sum_along_embedding_le {Job Slot : Type*} [Fintype Job] [Fintype Slot]
    (embedding : Job ↪ Slot) (f : Slot → ℕ) :
    (∑ x : Job, f (embedding x)) ≤ ∑ slot : Slot, f slot := by
  classical
  calc
    (∑ x : Job, f (embedding x)) = ∑ slot ∈ Finset.univ.image embedding, f slot :=
      (Finset.sum_image (fun _ _ _ _ h => embedding.injective h)).symm
    _ ≤ ∑ slot : Slot, f slot :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)

/-- Every finite requested-output family with at most `n*d` positions admits
one fixed assignment with at most `d` positions per machine and weighted load
at most its average plus the maximum position weight. Positions are padded
with zero-weight dummy slots, then assigned by the actual batch permutations.
The theorem does not require a nonempty machine type: the cardinality bound
forces the output family to be empty when `n = 0`. -/
theorem exists_balanced_output_assignment {Job : Type*} [Fintype Job]
    (n d W : ℕ) (weights : Job → ℕ)
    (hcard : Fintype.card Job ≤ n * d) (hw : ∀ x, weights x ≤ W) :
    ∃ assignment : Job → Fin n,
      (∀ i : Fin n, assignedCount assignment i ≤ d) ∧
      ∀ i : Fin n, n * weightedLoad weights assignment i ≤
        (∑ x : Job, weights x) + n * W := by
  classical
  have hc : Fintype.card Job ≤ Fintype.card (Fin d × Fin n) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using hcard
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le hc
  let padded := paddedWeight embedding weights
  obtain ⟨slots, hcount, hweight⟩ := exists_balanced_slot_assignment n d W
    (fun t j => padded (t, j)) (fun t j => paddedWeight_le embedding weights W hw (t, j))
  have htotal : (∑ t : Fin d, ∑ j : Fin n, padded (t, j)) = ∑ x : Job, weights x := by
    rw [← Fintype.sum_prod_type]
    exact paddedWeight_sum embedding weights
  refine ⟨fun x => slots (embedding x), ?_, ?_⟩
  · intro i
    calc
      assignedCount (fun x => slots (embedding x)) i ≤ assignedCount slots i := by
        exact sum_along_embedding_le embedding (fun slot => if slots slot = i then 1 else 0)
      _ = d := hcount i
  · intro i
    have hle : weightedLoad weights (fun x => slots (embedding x)) i ≤
        weightedLoad padded slots i := by
      unfold weightedLoad
      calc
        (∑ x : Job, if slots (embedding x) = i then weights x else 0) =
            ∑ x : Job, if slots (embedding x) = i then padded (embedding x) else 0 := by
          simp only [padded, paddedWeight_apply]
        _ ≤ ∑ slot : Fin d × Fin n, if slots slot = i then padded slot else 0 :=
          sum_along_embedding_le embedding (fun slot => if slots slot = i then padded slot else 0)
    exact (Nat.mul_le_mul_left n hle).trans (by simpa only [htotal] using hweight i)

end SparseMM.OutputAssignment
