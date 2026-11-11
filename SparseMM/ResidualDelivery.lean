module

public import SparseMM.Masks
public import SparseMM.Clustering
public import SparseMM.Counting
public import SparseMM.Routing

@[expose] public section

namespace SparseMM.ResidualDelivery

open scoped BigOperators

variable {n d t : ℕ} (A B Q R : Mask n)

/-- Each occurrence is a particular product for a particular requested output.
Equal numerical products remain distinct messages. -/
abbrev Packet := Σ q : {p // p ∈ Q},
  {j : Fin n // q.val ∈ R ∧ j ∈ middleSet A B q.val}

def source (p : Packet A B Q R) : Fin n := p.2.val

def destination (out : {p // p ∈ Q} → Fin n) (p : Packet A B Q R) : Fin n :=
  out p.1

theorem source_load (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hsparse : ResidualSparse d t R) (j : Fin n) :
    Counting.count (source A B Q R) j < t := by
  classical
  let f : {p : Packet A B Q R // source A B Q R p = j} →
      {q // q ∈ residualProducts A B R j} := fun p =>
    ⟨p.val.1.val, by
      have hp := p.val.2.property
      have hj : p.val.2.val = j := p.property
      simp only [middleSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [residualProducts, Finset.mem_filter]
      exact ⟨hp.1, by simpa only [← hj] using hp.2⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨q, m⟩, hp⟩ ⟨⟨q', m'⟩, hp'⟩ he
    have hq : q = q' := by
      apply Subtype.ext
      exact congrArg (fun x : {q // q ∈ residualProducts A B R j} => x.val) he
    subst q'
    change m.val = j at hp
    change m'.val = j at hp'
    have hm : m = m' := Subtype.ext (hp.trans hp'.symm)
    subst m'
    rfl
  have hcount := Counting.count_le_card_of_injective (source A B Q R) j
    (residualProducts A B R j) f hf
  have hsmall := hsparse (colMask A j) (rowMask B j) (hA.2 j) (hB.1 j)
  rw [← residualProducts_eq_rectangle] at hsmall
  exact hcount.trans_lt hsmall

theorem destination_load (out : {p // p ∈ Q} → Fin n) (node : Fin n) :
    Counting.count (destination A B Q R out) node =
      Counting.load out (fun q => residualWeight A B R q.val) node := by
  classical
  rw [Counting.count_eq_load]
  unfold Counting.load destination
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hn : out q = node
  · simp only [hn, ite_true]
    by_cases hr : q.val ∈ R
    · simp [residualWeight, hr, Fintype.card_subtype]
    · simp [residualWeight, hr]
  · simp [hn]

/-- The residual phase admits a fixed collision-free schedule. Its only
placement premise is the public output-weight bound, established separately. -/
theorem exists_schedule (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hsparse : ResidualSparse d t R)
    (out : {p // p ∈ Q} → Fin n)
    (hout : ∀ node, Counting.load out (fun q => residualWeight A B R q.val) node ≤ t + d) :
    ∃ slot : Packet A B Q R → Fin (2 * (t + d)),
      Routing.LegalOn Finset.univ (source A B Q R)
        (destination A B Q R out) slot := by
  classical
  apply Routing.exists_schedule
  · intro node
    exact (Nat.le_of_lt (source_load A B Q R hA hB hsparse node)).trans (Nat.le_add_right _ _)
  · intro node
    change Counting.count (destination A B Q R out) node ≤ t + d
    rw [destination_load]
    exact hout node

end SparseMM.ResidualDelivery
