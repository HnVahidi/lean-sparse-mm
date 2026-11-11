module

public import SparseMM.Clustering
public import SparseMM.Masks

@[expose] public section

namespace SparseMM

open scoped BigOperators

def clusterRows {n : ℕ} (C : Mask n) : Finset (Fin n) := C.image Prod.fst

def clusterCols {n : ℕ} (C : Mask n) : Finset (Fin n) := C.image Prod.snd

theorem clusterRows_card_le {n d : ℕ} (C : Mask n) (hC : FitsRectangle d C) :
    (clusterRows C).card ≤ d := by
  obtain ⟨rows, cols, hr, hc, hsub⟩ := hC
  apply (Finset.card_le_card (show clusterRows C ⊆ rows from ?_)).trans hr
  intro i hi
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
  exact (Finset.mem_product.mp (hsub hp)).1

theorem clusterCols_card_le {n d : ℕ} (C : Mask n) (hC : FitsRectangle d C) :
    (clusterCols C).card ≤ d := by
  obtain ⟨rows, cols, hr, hc, hsub⟩ := hC
  apply (Finset.card_le_card (show clusterCols C ⊆ cols from ?_)).trans hc
  intro k hk
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
  exact (Finset.mem_product.mp (hsub hp)).2

/-- The number of allowed inputs a helper needs when it handles middle index
`j` for cluster `C`. Values are counted once, regardless of numerical zeros. -/
def clusterInputCost {n : ℕ} (A B C : Mask n) (j : Fin n) : ℕ :=
  (colMask A j ∩ clusterRows C).card + (rowMask B j ∩ clusterCols C).card

theorem clusterInputCost_le {n d : ℕ} (A B C : Mask n)
    (hA : UniformSparse A d) (hB : UniformSparse B d) (j : Fin n) :
    clusterInputCost A B C j ≤ 2 * d := by
  have h1 := (Finset.card_le_card (Finset.inter_subset_left :
    colMask A j ∩ clusterRows C ⊆ colMask A j)).trans (hA.2 j)
  have h2 := (Finset.card_le_card (Finset.inter_subset_left :
    rowMask B j ∩ clusterCols C ⊆ rowMask B j)).trans (hB.1 j)
  unfold clusterInputCost
  omega

theorem sum_restricted_columns {n : ℕ} (A : Mask n) (rows : Finset (Fin n)) :
    (∑ j : Fin n, (colMask A j ∩ rows).card) =
      ∑ i ∈ rows, (rowMask A i).card := by
  classical
  have hf : ∀ j, colMask A j ∩ rows = rows.filter (fun i => (i, j) ∈ A) := by
    intro j
    ext i
    simp [colMask, and_comm]
  simp_rw [hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [rowMask, Finset.sum_filter]

theorem sum_restricted_rows {n : ℕ} (B : Mask n) (cols : Finset (Fin n)) :
    (∑ j : Fin n, (rowMask B j ∩ cols).card) =
      ∑ k ∈ cols, (colMask B k).card := by
  classical
  have hf : ∀ j, rowMask B j ∩ cols = cols.filter (fun k => (j, k) ∈ B) := by
    intro j
    ext k
    simp [rowMask, and_comm]
  simp_rw [hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [colMask, Finset.sum_filter]

/-- The complete input weight of a cluster is at most `2*d*d` (Lemma 7). -/
theorem sum_clusterInputCost_le {n d : ℕ} (A B C : Mask n)
    (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hC : FitsRectangle d C) :
    (∑ j : Fin n, clusterInputCost A B C j) ≤ 2 * d * d := by
  unfold clusterInputCost
  rw [Finset.sum_add_distrib, sum_restricted_columns, sum_restricted_rows]
  have h1 : (∑ i ∈ clusterRows C, (rowMask A i).card) ≤ d * d := by
    calc
      _ ≤ ∑ _i ∈ clusterRows C, d := Finset.sum_le_sum fun i _ => hA.1 i
      _ = (clusterRows C).card * d := by simp
      _ ≤ d * d := Nat.mul_le_mul_right d (clusterRows_card_le C hC)
  have h2 : (∑ k ∈ clusterCols C, (colMask B k).card) ≤ d * d := by
    calc
      _ ≤ ∑ _k ∈ clusterCols C, d := Finset.sum_le_sum fun k _ => hB.2 k
      _ = (clusterCols C).card * d := by simp
      _ ≤ d * d := Nat.mul_le_mul_right d (clusterCols_card_le C hC)
  nlinarith

/-- Distinct positions in a disjoint list of clusters yield disjoint sets. -/
theorem Clustering.get_disjoint {n d t : ℕ} {Q : Mask n}
    (D : Clustering Q d t) (a b : Fin D.clusters.length) (hab : a ≠ b) :
    Disjoint D.clusters[a] D.clusters[b] := by
  have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · exact D.pairwise_disjoint.rel_getElem_of_lt a.isLt b.isLt hlt
  · exact (D.pairwise_disjoint.rel_getElem_of_lt b.isLt a.isLt hlt).symm

theorem Clustering.unique_cluster_index {n d t : ℕ} {Q : Mask n}
    (D : Clustering Q d t) (a b : Fin D.clusters.length) (p : Fin n × Fin n)
    (ha : p ∈ D.clusters[a]) (hb : p ∈ D.clusters[b]) : a = b := by
  by_contra hne
  exact Finset.disjoint_left.mp (D.get_disjoint a b hne) ha hb

/-- Cluster indices whose selected output positions meet row `i`. -/
def rowClusters {n d t : ℕ} {Q : Mask n} (D : Clustering Q d t) (i : Fin n) :
    Finset (Fin D.clusters.length) :=
  Finset.univ.filter fun c => i ∈ clusterRows D.clusters[c]

/-- Cluster indices whose selected output positions meet column `k`. -/
def colClusters {n d t : ℕ} {Q : Mask n} (D : Clustering Q d t) (k : Fin n) :
    Finset (Fin D.clusters.length) :=
  Finset.univ.filter fun c => k ∈ clusterCols D.clusters[c]

theorem rowClusters_card_le_row {n d t : ℕ} {Q : Mask n}
    (D : Clustering Q d t) (i : Fin n) :
    (rowClusters D i).card ≤ (rowMask Q i).card := by
  classical
  have hex : ∀ c : rowClusters D i, ∃ k : rowMask Q i, (i, k.val) ∈ D.clusters[c.val] := by
    intro c
    have hc := (Finset.mem_filter.mp c.property).2
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hc
    have hmem : (i, p.2) ∈ D.clusters[c.val] := by simpa [← hpi] using hp
    have hQ : (i, p.2) ∈ Q := D.cluster_sub _ (List.getElem_mem _) hmem
    exact ⟨⟨p.2, by simpa [rowMask] using hQ⟩, hmem⟩
  let f : rowClusters D i → rowMask Q i := fun c => Classical.choose (hex c)
  apply Finset.card_le_card_of_injective (f := f)
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hdis := D.get_disjoint a.val b.val hne
  have ha := Classical.choose_spec (hex a)
  have hb := Classical.choose_spec (hex b)
  change (i, (f a).val) ∈ D.clusters[a.val] at ha
  change (i, (f b).val) ∈ D.clusters[b.val] at hb
  have heq : (f a).val = (f b).val := congrArg Subtype.val hab
  apply Finset.disjoint_left.mp hdis ha
  rw [← heq] at hb
  exact hb

theorem colClusters_card_le_col {n d t : ℕ} {Q : Mask n}
    (D : Clustering Q d t) (k : Fin n) :
    (colClusters D k).card ≤ (colMask Q k).card := by
  classical
  have hex : ∀ c : colClusters D k, ∃ i : colMask Q k, (i.val, k) ∈ D.clusters[c.val] := by
    intro c
    have hc := (Finset.mem_filter.mp c.property).2
    obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hc
    have hmem : (p.1, k) ∈ D.clusters[c.val] := by simpa [← hpk] using hp
    have hQ : (p.1, k) ∈ Q := D.cluster_sub _ (List.getElem_mem _) hmem
    exact ⟨⟨p.1, by simpa [colMask] using hQ⟩, hmem⟩
  let f : colClusters D k → colMask Q k := fun c => Classical.choose (hex c)
  apply Finset.card_le_card_of_injective (f := f)
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hdis := D.get_disjoint a.val b.val hne
  have ha := Classical.choose_spec (hex a)
  have hb := Classical.choose_spec (hex b)
  change ((f a).val, k) ∈ D.clusters[a.val] at ha
  change ((f b).val, k) ∈ D.clusters[b.val] at hb
  have heq : (f a).val = (f b).val := congrArg Subtype.val hab
  apply Finset.disjoint_left.mp hdis ha
  rw [← heq] at hb
  exact hb

/-- An allowed left input is needed by at most `d` clusters, because its row
can meet at most `d` pairwise disjoint clusters (Lemma 8). -/
theorem rowClusters_card_le {n d t : ℕ} {Q : Mask n}
    (D : Clustering Q d t) (hQ : UniformSparse Q d) (i : Fin n) :
    (rowClusters D i).card ≤ d :=
  (rowClusters_card_le_row D i).trans (hQ.1 i)

/-- The analogous fanout bound for a right input uses its column. -/
theorem colClusters_card_le {n d t : ℕ} {Q : Mask n}
    (D : Clustering Q d t) (hQ : UniformSparse Q d) (k : Fin n) :
    (colClusters D k).card ≤ d :=
  (colClusters_card_le_col D k).trans (hQ.2 k)

end SparseMM
