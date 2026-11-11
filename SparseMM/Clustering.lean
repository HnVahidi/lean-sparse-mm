module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM

variable {I K : Type*} [DecidableEq I] [DecidableEq K]

/-- A set of requested coordinates contained in at most `d` rows and columns. -/
def FitsRectangle (d : ℕ) (C : Finset (I × K)) : Prop :=
  ∃ rows : Finset I, ∃ cols : Finset K,
    rows.card ≤ d ∧ cols.card ≤ d ∧ C ⊆ rows ×ˢ cols

/-- Every rectangle with at most `d` rows and columns contains fewer than `t`
remaining requested coordinates. -/
def ResidualSparse (d t : ℕ) (R : Finset (I × K)) : Prop :=
  ∀ rows : Finset I, ∀ cols : Finset K,
    rows.card ≤ d → cols.card ≤ d → (R ∩ rows ×ˢ cols).card < t

/-- The complete finite certificate produced by dense-rectangle extraction.
The `accounting` field includes the residual, so the cluster count cannot hide
overlaps or discarded output positions. -/
structure Clustering (Q : Finset (I × K)) (d t : ℕ) where
  clusters : List (Finset (I × K))
  residual : Finset (I × K)
  cluster_sub : ∀ C ∈ clusters, C ⊆ Q
  cluster_card : ∀ C ∈ clusters, C.card = t
  cluster_rectangle : ∀ C ∈ clusters, FitsRectangle d C
  pairwise_disjoint : clusters.Pairwise Disjoint
  residual_sub : residual ⊆ Q
  residual_disjoint : ∀ C ∈ clusters, Disjoint C residual
  cover : ∀ p, p ∈ Q ↔ p ∈ residual ∨ ∃ C ∈ clusters, p ∈ C
  sparse : ResidualSparse d t residual
  accounting : clusters.length * t + residual.card = Q.card

/-- Dense-rectangle extraction always terminates and partitions *all* requested
coordinates. It uses only the finite output mask, `d`, and `t`; selecting a fixed
classical witness therefore gives the same decomposition to every machine. -/
theorem exists_clustering (Q : Finset (I × K)) (d t : ℕ) (ht : 0 < t) :
    Nonempty (Clustering Q d t) := by
  classical
  induction Q using Finset.strongInductionOn with
  | _ Q ih =>
    by_cases hs : ResidualSparse d t Q
    · exact ⟨{
        clusters := []
        residual := Q
        cluster_sub := by simp
        cluster_card := by simp
        cluster_rectangle := by simp
        pairwise_disjoint := by simp
        residual_sub := Finset.Subset.refl Q
        residual_disjoint := by simp
        cover := by simp
        sparse := hs
        accounting := by simp }⟩
    · unfold ResidualSparse at hs
      push Not at hs
      obtain ⟨rows, cols, hrows, hcols, hdense⟩ := hs
      obtain ⟨C, hC, hCt⟩ := Finset.exists_subset_card_eq hdense
      have hCQ : C ⊆ Q := hC.trans Finset.inter_subset_left
      have hCR : C ⊆ rows ×ˢ cols := hC.trans Finset.inter_subset_right
      have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨D⟩ := ih (Q \ C) (Finset.sdiff_ssubset hCQ hCnonempty)
      have hCtail : ∀ E ∈ D.clusters, Disjoint C E := by
        intro E hE
        apply Finset.disjoint_left.mpr
        intro p hpC hpE
        have := D.cluster_sub E hE hpE
        exact (Finset.mem_sdiff.mp this).2 hpC
      have hCres : Disjoint C D.residual := by
        apply Finset.disjoint_left.mpr
        intro p hpC hpR
        exact (Finset.mem_sdiff.mp (D.residual_sub hpR)).2 hpC
      refine ⟨{
        clusters := C :: D.clusters
        residual := D.residual
        cluster_sub := ?_
        cluster_card := ?_
        cluster_rectangle := ?_
        pairwise_disjoint := ?_
        residual_sub := D.residual_sub.trans Finset.sdiff_subset
        residual_disjoint := ?_
        cover := ?_
        sparse := D.sparse
        accounting := ?_ }⟩
      · intro E hE
        rcases List.mem_cons.mp hE with rfl | hE
        · exact hCQ
        · exact (D.cluster_sub E hE).trans Finset.sdiff_subset
      · intro E hE
        rcases List.mem_cons.mp hE with rfl | hE
        · exact hCt
        · exact D.cluster_card E hE
      · intro E hE
        rcases List.mem_cons.mp hE with rfl | hE
        · exact ⟨rows, cols, hrows, hcols, hCR⟩
        · exact D.cluster_rectangle E hE
      · exact List.pairwise_cons.mpr ⟨hCtail, D.pairwise_disjoint⟩
      · intro E hE
        rcases List.mem_cons.mp hE with rfl | hE
        · exact hCres
        · exact D.residual_disjoint E hE
      · intro p
        constructor
        · intro hpQ
          by_cases hpC : p ∈ C
          · exact Or.inr ⟨C, List.mem_cons_self, hpC⟩
          · rcases (D.cover p).mp (Finset.mem_sdiff.mpr ⟨hpQ, hpC⟩) with hpR | ⟨E, hE, hpE⟩
            · exact Or.inl hpR
            · exact Or.inr ⟨E, List.mem_cons_of_mem _ hE, hpE⟩
        · rintro (hpR | ⟨E, hE, hpE⟩)
          · exact Finset.sdiff_subset (D.residual_sub hpR)
          · rcases List.mem_cons.mp hE with rfl | hE
            · exact hCQ hpE
            · exact Finset.sdiff_subset (D.cluster_sub E hE hpE)
      · have hdiff := Finset.card_sdiff_add_card_eq_card hCQ
        have haccount := D.accounting
        simp only [List.length_cons, Nat.add_mul, one_mul]
        omega

/-- The number of extracted clusters times their exact size never exceeds
the number of requested output positions (Lemma 6, before rounding). -/
theorem Clustering.cluster_count_bound {Q : Finset (I × K)} {d t : ℕ}
    (D : Clustering Q d t) : D.clusters.length * t ≤ Q.card := by
  have := D.accounting
  omega

/-- With threshold `d*h`, disjoint teams of `h` helpers fit in `n` machines
whenever the output mask has at most `n*d` marked positions. -/
theorem Clustering.cluster_teams_fit {Q : Finset (I × K)} {d h n : ℕ}
    (D : Clustering Q d (d * h)) (hd : 0 < d) (hQ : Q.card ≤ n * d) :
    D.clusters.length * h ≤ n := by
  have hcount := D.cluster_count_bound
  nlinarith

end SparseMM
