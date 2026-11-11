module

public import SparseMM.HelperPlan
public import SparseMM.Routing

@[expose] public section

namespace SparseMM.InputGather

open HelperPlan

/-- The contracted index identifies the processor that evaluates this input's
residual subproducts: column `j` of the left input, row `j` of the right. -/
def destination {n : ℕ} {A B : Mask n} : Input A B → Fin n
  | Sum.inl e => e.val.2
  | Sum.inr e => e.val.1

abbrev middle {n : ℕ} {A B : Mask n} : Input A B → Fin n := destination

/-- A processor gathers at most one sparse column and one sparse row. -/
theorem destination_count_le {n d : ℕ} (A B : Mask n)
    (hA : UniformSparse A d) (hB : UniformSparse B d) (j : Fin n) :
    Counting.count (destination (A := A) (B := B)) j ≤ 2 * d := by
  classical
  rw [Counting.count_eq_card_fiber]
  let f : {e : Input A B // destination e = j} →
      Sum {i // i ∈ colMask A j} {k // k ∈ rowMask B j} := fun e => by
    rcases e with ⟨e, he⟩
    cases e with
    | inl a =>
        refine Sum.inl ⟨a.val.1, ?_⟩
        simp only [destination] at he
        simp only [colMask, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [← he] using a.property
    | inr b =>
        refine Sum.inr ⟨b.val.2, ?_⟩
        simp only [destination] at he
        simp only [rowMask, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [← he] using b.property
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            simp only [f, Sum.inl.injEq, Subtype.mk.injEq] at hab
            apply congrArg Sum.inl
            apply Subtype.ext
            apply Prod.ext
            · exact hab
            · exact ha.trans hb.symm
        | inr b => cases hab
    | inr a =>
        cases b with
        | inl b => cases hab
        | inr b =>
            simp only [f, Sum.inr.injEq, Subtype.mk.injEq] at hab
            apply congrArg Sum.inr
            apply Subtype.ext
            apply Prod.ext
            · exact ha.trans hb.symm
            · exact hab
  have hcard := Fintype.card_le_of_injective f hf
  have ha := hA.2 j
  have hb := hB.1 j
  simp only [Fintype.card_sum, Fintype.card_coe] at hcard
  omega

/-- The residual gather has a public collision-free schedule. The source map
is the actual initial input distribution; no redistribution is assumed free. -/
theorem exists_schedule {n d : ℕ} (A B : Mask n)
    (hA : UniformSparse A d) (hB : UniformSparse B d)
    (K : ℕ) (original : Input A B → Fin n)
    (horiginal : ∀ m, Counting.count original m ≤ K * d) :
    ∃ slot : Input A B → Fin (2 * (K * d + 2 * d)),
      Routing.LegalOn Finset.univ original destination slot := by
  apply Routing.exists_schedule original destination (K * d + 2 * d)
  · intro m
    exact (horiginal m).trans (Nat.le_add_right _ _)
  · intro m
    exact (destination_count_le A B hA hB m).trans (Nat.le_add_left _ _)

end SparseMM.InputGather
