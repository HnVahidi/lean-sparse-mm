module

public import SparseMM.OutputAssignment
public import SparseMM.ResidualDelivery

@[expose] public section

namespace SparseMM

open scoped BigOperators

theorem total_residual_weight {n : ℕ} (A B Q R : Mask n) (hRQ : R ⊆ Q) :
    (∑ q : {p // p ∈ Q}, residualWeight A B R q.val) =
      ∑ p ∈ R, (middleSet A B p).card := by
  classical
  rw [Finset.sum_coe_sort Q (residualWeight A B R)]
  simp only [residualWeight]
  rw [← Finset.sum_filter]
  have heq : Q.filter (fun p => p ∈ R) = R := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => hp.2, fun hp => ⟨hRQ hp, hp⟩⟩
  rw [heq]

theorem residual_weight_lt {n d t : ℕ} (hn : 0 < n)
    (A B Q R : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hRQ : R ⊆ Q) (hs : ResidualSparse d t R) :
    (∑ q : {p // p ∈ Q}, residualWeight A B R q.val) < n * t := by
  rw [total_residual_weight A B Q R hRQ, ← residual_contributions_double_count]
  have hsmall (j : Fin n) : (residualProducts A B R j).card < t := by
    rw [residualProducts_eq_rectangle]
    exact hs _ _ (hA.2 j) (hB.1 j)
  calc
    _ < ∑ _j : Fin n, t := by
      apply Finset.sum_lt_sum
      · intro j _
        exact (hsmall j).le
      · exact ⟨⟨0, hn⟩, Finset.mem_univ _, hsmall _⟩
    _ = _ := by simp

/-- One public output assignment simultaneously balances output counts and
residual contributions. The assignment quantifies before numerical inputs. -/
theorem exists_output_plan {n d t : ℕ} (hn : 0 < n)
    (A B Q R : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hQ : UniformSparse Q d) (hRQ : R ⊆ Q) (hs : ResidualSparse d t R) :
    ∃ out : {p // p ∈ Q} → Fin n,
      (∀ node, Counting.count out node ≤ d) ∧
      (∀ node, Counting.load out (fun q => residualWeight A B R q.val) node ≤ t + d) := by
  classical
  have hcard : Fintype.card {p // p ∈ Q} ≤ n * d := by
    simpa using mask_card_le Q hQ
  have hweight (q : {p // p ∈ Q}) : residualWeight A B R q.val ≤ d :=
    residualWeight_le A B R hA q.val
  obtain ⟨out, hc, hw⟩ := OutputAssignment.exists_balanced_output_assignment n d d
    (fun q : {p // p ∈ Q} => residualWeight A B R q.val) hcard hweight
  refine ⟨out, ?_, ?_⟩
  · intro node
    rw [Counting.count_eq_load]
    exact hc node
  intro node
  have htotal := residual_weight_lt hn A B Q R hA hB hRQ hs
  have hb := hw node
  apply Nat.le_of_mul_le_mul_left (c := n) (hc := hn)
  change n * Counting.load out (fun q => residualWeight A B R q.val) node ≤
    (∑ q : {p // p ∈ Q}, residualWeight A B R q.val) + n * d at hb
  nlinarith

/-- The strict residual bound advertised in Lemma 10. The total number of
residual contributions is strictly below `n*t`, so no rounding slack is lost. -/
theorem exists_strict_output_plan {n d t : ℕ} (hn : 0 < n)
    (A B Q R : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hQ : UniformSparse Q d) (hRQ : R ⊆ Q) (hs : ResidualSparse d t R) :
    ∃ out : {p // p ∈ Q} → Fin n,
      (∀ node, Counting.count out node ≤ d) ∧
      (∀ node, Counting.load out (fun q => residualWeight A B R q.val) node < t + d) := by
  classical
  have hcard : Fintype.card {p // p ∈ Q} ≤ n * d := by
    simpa using mask_card_le Q hQ
  obtain ⟨out, hc, hw⟩ := OutputAssignment.exists_balanced_output_assignment n d d
    (fun q : {p // p ∈ Q} => residualWeight A B R q.val) hcard
    (fun q => residualWeight_le A B R hA q.val)
  refine ⟨out, ?_, ?_⟩
  · intro node
    rw [Counting.count_eq_load]
    exact hc node
  · intro node
    have htotal := residual_weight_lt hn A B Q R hA hB hRQ hs
    have hb := hw node
    change n * Counting.load out (fun q => residualWeight A B R q.val) node ≤
      (∑ q : {p // p ∈ Q}, residualWeight A B R q.val) + n * d at hb
    nlinarith

end SparseMM
