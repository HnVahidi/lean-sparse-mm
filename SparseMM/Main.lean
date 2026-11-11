module

public import SparseMM.Program
public import SparseMM.Complexity

@[expose] public section

namespace SparseMM

universe u

/-- **Theorem 4, finite operational form.** Public masks and the original
input distribution determine one distributed program and one balanced output
assignment before any numerical inputs are supplied. Every requested answer
is correct over an arbitrary semiring. Every phase of the program uses only
local computation and verified one-send/one-receive redistributions.

The fixed constant `K` makes the paper's `O(d)` initial load explicit. Scalar
messages implement the word model under the paper's stated encoding premise. -/
theorem supported_sparse_mm {n d K : ℕ} (hn : 0 < n) (hd : 0 < d)
    (A B Q : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hQ : UniformSparse Q d) (original : HelperPlan.Input A B → Fin n)
    (horiginal : ∀ node, Counting.count original node ≤ K * d)
    (S : Type u) [Semiring S] :
    ∃ out : {p // p ∈ Q} → Fin n, ∃ State : Type u,
      ∃ code : LocalPipeline.Program (Fin n) (HelperPlan.Input A B → Option S)
          State S ({p // p ∈ Q} → S),
        (∀ node, Counting.count out node ≤ d) ∧
        code.rounds ≤ (4 * K + 40) * threshold d ∧
        (code.rounds : ℝ) ≤ (8 * K + 80) * (d : ℝ) * Real.sqrt d ∧
        ∀ U V : Matrix (Fin n) (Fin n) S,
          Algebra.SupportedBy U A → Algebra.SupportedBy V B →
          ∀ q : {p // p ∈ Q},
            code.output (SupportedProgram.views original U V) (out q) q =
              (U * V) q.val.1 q.val.2 := by
  classical
  obtain ⟨P⟩ := exists_public_plan (K := K) hn hd A B Q hA hB hQ original horiginal
  refine ⟨P.out, SupportedProgram.State P S, SupportedProgram.program P,
    P.output_count, ?_, ?_, ?_⟩
  · rw [SupportedProgram.program_rounds]
    exact (P.rounds_le).trans (by nlinarith)
  · rw [SupportedProgram.program_rounds]
    exact roundBudget_le_sqrt hd K
  · intro U V hU hV q
    exact SupportedProgram.output_correct P U V hU hV q

end SparseMM
