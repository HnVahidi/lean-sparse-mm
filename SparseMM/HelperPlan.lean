module

public import SparseMM.ClusterLoads
public import SparseMM.Balancing
public import SparseMM.Counting
public import SparseMM.Rounding
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace SparseMM.HelperPlan

open scoped BigOperators

abbrev Input {n : ℕ} (A B : Mask n) :=
  Sum {e // e ∈ A} {e // e ∈ B}

abbrev Helper {n d t : ℕ} {Q : Mask n} (D : Clustering Q d t) (h : ℕ) :=
  Fin D.clusters.length × Fin h

/-- One labelled copy of an allowed input, needed by one cluster and one
middle index. Its helper is determined by the assignment of that middle index. -/
abbrev Request {n d t : ℕ} (A B : Mask n) {Q : Mask n} (D : Clustering Q d t) :=
  Σ c : Fin D.clusters.length, Σ j : Fin n,
    Sum {i // i ∈ colMask A j ∩ clusterRows D.clusters[c]}
      {k // k ∈ rowMask B j ∩ clusterCols D.clusters[c]}

def Request.input {n d t : ℕ} {A B Q : Mask n} {D : Clustering Q d t}
    (r : Request A B D) : Input A B :=
  match r.2.2 with
  | Sum.inl i => Sum.inl ⟨(i.val, r.2.1), by
      have := (Finset.mem_inter.mp i.property).1
      simpa [colMask] using this⟩
  | Sum.inr k => Sum.inr ⟨(r.2.1, k.val), by
      have := (Finset.mem_inter.mp k.property).1
      simpa [rowMask] using this⟩

def Request.helper {n d t h : ℕ} {A B Q : Mask n} {D : Clustering Q d t}
    (assignment : Fin D.clusters.length → Fin n → Fin h) (r : Request A B D) :
    Helper D h := (r.1, assignment r.1 r.2.1)

/-- An actual bounded assignment for every cluster, constructed from public masks. -/
theorem exists_helper_assignment {n d : ℕ} {A B Q : Mask n}
    (D : Clustering Q d (threshold d))
    (hA : UniformSparse A d) (hB : UniformSparse B d) :
    ∃ assignment : Fin D.clusters.length → Fin n → Fin (teamSize d),
      ∀ c b, Balancing.binLoad (clusterInputCost A B D.clusters[c])
        (assignment c) b ≤ 4 * threshold d := by
  classical
  have hex : ∀ c : Fin D.clusters.length, ∃ a : Fin n → Fin (teamSize d),
      ∀ b, Balancing.binLoad (clusterInputCost A B D.clusters[c]) a b ≤
        4 * threshold d := by
    intro c
    have htotal := sum_clusterInputCost_le A B D.clusters[c] hA hB
      (D.cluster_rectangle _ (List.getElem_mem _))
    have hsquare := degree_le_teamSize_sq d
    have htotal' : (∑ j : Fin n, clusterInputCost A B D.clusters[c] j) ≤
        teamSize d * (2 * threshold d) := by
      unfold threshold
      nlinarith
    obtain ⟨a, ha⟩ := Balancing.exists_assignment_le_average_add
      (teamSize d) n (2 * threshold d) (2 * d) (teamSize_pos d)
      (clusterInputCost A B D.clusters[c]) (clusterInputCost_le A B D.clusters[c] hA hB)
      htotal'
    exact ⟨a, fun b => (ha b).trans (by have := degree_le_threshold d; omega)⟩
  choose assignment hbound using hex
  exact ⟨assignment, hbound⟩

/-- The disjoint helper teams admit an actual injection into the processors. -/
theorem exists_helper_placement {n d : ℕ} {Q : Mask n}
    (D : Clustering Q d (threshold d)) (hd : 0 < d) (hQ : UniformSparse Q d) :
    Nonempty (Helper D (teamSize d) ↪ Fin n) := by
  classical
  have hcount := D.cluster_teams_fit hd (mask_card_le Q hQ)
  have hcard : Fintype.card (Helper D (teamSize d)) ≤ n := by
    simpa [Helper, Fintype.card_prod] using hcount
  let f : Helper D (teamSize d) → Fin n := fun x =>
    ⟨(Fintype.equivFin _ x).val, lt_of_lt_of_le (Fintype.equivFin _ x).isLt hcard⟩
  refine ⟨⟨f, ?_⟩⟩
  intro a b hab
  apply (Fintype.equivFin _).injective
  apply Fin.ext
  exact congrArg (fun x : Fin n => x.val) hab

/-- Each helper receives exactly its assigned input weight. -/
theorem helper_request_count {n d t h : ℕ} {A B Q : Mask n}
    (D : Clustering Q d t) (assignment : Fin D.clusters.length → Fin n → Fin h)
    (c : Fin D.clusters.length) (b : Fin h) :
    Counting.count (Request.helper (A := A) (B := B) assignment) (c, b) =
      Balancing.binLoad (clusterInputCost A B D.clusters[c]) (assignment c) b := by
  classical
  rw [Counting.count_eq_load]
  unfold Counting.load
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · unfold Balancing.binLoad
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hab : assignment c j = b
    · simp only [Request.helper, hab,
        ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
        mul_one, Fintype.card_sum, Fintype.card_coe, clusterInputCost]
    · simp [Request.helper, hab]
  · intro c' hc' hne
    apply Finset.sum_eq_zero
    intro j hj
    simp [Request.helper, hne]
  · simp

/-- A copy label and its cluster uniquely specify a requested input copy. -/
theorem Request.ext_input {n d t : ℕ} {A B Q : Mask n} {D : Clustering Q d t}
    (a b : Request A B D) (hc : a.1 = b.1) (hi : a.input = b.input) : a = b := by
  rcases a with ⟨ca, ja, sa⟩
  rcases b with ⟨cb, jb, sb⟩
  dsimp at hc
  subst cb
  cases sa with
  | inl ia =>
      cases sb with
      | inl ib =>
          simp only [Request.input, Sum.inl.injEq, Subtype.mk.injEq] at hi
          have hj : ja = jb := congrArg Prod.snd hi
          subst jb
          have hi' : ia = ib := Subtype.ext (congrArg Prod.fst hi)
          cases hi'
          rfl
      | inr kb => cases hi
  | inr ka =>
      cases sb with
      | inl ib => cases hi
      | inr kb =>
          simp only [Request.input, Sum.inr.injEq, Subtype.mk.injEq] at hi
          have hj : ja = jb := congrArg Prod.fst hi
          subst jb
          have hk : ka = kb := Subtype.ext (congrArg Prod.snd hi)
          cases hk
          rfl

theorem Request.left_row {n d t : ℕ} {A B Q : Mask n} {D : Clustering Q d t}
    (r : Request A B D) (e : {e // e ∈ A}) (he : r.input = Sum.inl e) :
    e.val.1 ∈ clusterRows D.clusters[r.1] := by
  rcases r with ⟨c, j, s⟩
  cases s with
  | inl i =>
      simp only [Request.input, Sum.inl.injEq] at he
      have hi := (Finset.mem_inter.mp i.property).2
      simpa only [← he] using hi
  | inr k => cases he

theorem Request.right_col {n d t : ℕ} {A B Q : Mask n} {D : Clustering Q d t}
    (r : Request A B D) (e : {e // e ∈ B}) (he : r.input = Sum.inr e) :
    e.val.2 ∈ clusterCols D.clusters[r.1] := by
  rcases r with ⟨c, j, s⟩
  cases s with
  | inl i => cases he
  | inr k =>
      simp only [Request.input, Sum.inr.injEq] at he
      have hk := (Finset.mem_inter.mp k.property).2
      simpa only [← he] using hk

/-- Each allowed input has at most `d` requested copies across all helpers. -/
theorem input_request_count_le {n d t : ℕ} {A B Q : Mask n}
    (D : Clustering Q d t) (hQ : UniformSparse Q d) (e : Input A B) :
    Counting.count (Request.input (D := D)) e ≤ d := by
  classical
  cases e with
  | inl e =>
      let f : {r : Request A B D // r.input = Sum.inl e} →
          {c // c ∈ rowClusters D e.val.1} := fun r =>
        ⟨r.val.1, by simp only [rowClusters, Finset.mem_filter, Finset.mem_univ, true_and]
                     exact r.val.left_row e r.property⟩
      apply (Counting.count_le_card_of_injective (Request.input (D := D)) (Sum.inl e)
        (rowClusters D e.val.1) f ?_).trans (rowClusters_card_le D hQ e.val.1)
      intro a b hab
      apply Subtype.ext
      exact Request.ext_input a.val b.val (congrArg Subtype.val hab)
        (a.property.trans b.property.symm)
  | inr e =>
      let f : {r : Request A B D // r.input = Sum.inr e} →
          {c // c ∈ colClusters D e.val.2} := fun r =>
        ⟨r.val.1, by simp only [colClusters, Finset.mem_filter, Finset.mem_univ, true_and]
                     exact r.val.right_col e r.property⟩
      apply (Counting.count_le_card_of_injective (Request.input (D := D)) (Sum.inr e)
        (colClusters D e.val.2) f ?_).trans (colClusters_card_le D hQ e.val.2)
      intro a b hab
      apply Subtype.ext
      exact Request.ext_input a.val b.val (congrArg Subtype.val hab)
        (a.property.trans b.property.symm)

theorem physical_helper_count_le {n d t h L : ℕ} {A B Q : Mask n}
    (D : Clustering Q d t) (assignment : Fin D.clusters.length → Fin n → Fin h)
    (hload : ∀ c b, Balancing.binLoad (clusterInputCost A B D.clusters[c])
      (assignment c) b ≤ L) (place : Helper D h ↪ Fin n) (m : Fin n) :
    Counting.count (place ∘ Request.helper (A := A) (B := B) assignment) m ≤ L := by
  rw [Counting.count_eq_load]
  apply Counting.load_comp_injective _ _ place place.injective L ?_ m
  intro helper
  rw [← Counting.count_eq_load, helper_request_count]
  exact hload helper.1 helper.2

theorem total_requests_le {n d : ℕ} {A B Q : Mask n}
    (D : Clustering Q d (threshold d)) (assignment : Fin D.clusters.length → Fin n → Fin (teamSize d))
    (hload : ∀ c b, Balancing.binLoad (clusterInputCost A B D.clusters[c])
      (assignment c) b ≤ 4 * threshold d) (hd : 0 < d) (hQ : UniformSparse Q d) :
    Fintype.card (Request A B D) ≤ n * (4 * threshold d) := by
  classical
  obtain ⟨place⟩ := exists_helper_placement D hd hQ
  rw [← Counting.sum_count (place ∘ Request.helper (A := A) (B := B) assignment)]
  calc
    _ ≤ ∑ _m : Fin n, 4 * threshold d := Finset.sum_le_sum fun m _ =>
      physical_helper_count_le D assignment hload place m
    _ = _ := by simp

end SparseMM.HelperPlan
