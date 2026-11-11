module

public import SparseMM.ClusterLoads
public import SparseMM.Counting
public import SparseMM.Routing

@[expose] public section

namespace SparseMM.PartialDelivery

variable {n d t h : ℕ} {Q : Mask n} (D : Clustering Q d t)

abbrev Helper := Fin D.clusters.length × Fin h

/-- A separate partial sum is delivered for each cluster output and helper. -/
abbrev Packet := Σ q : {p // p ∈ Q},
  {helper : Helper (h := h) D // q.val ∈ D.clusters[helper.1]}

def helper (p : Packet (h := h) D) : Helper (h := h) D := p.2.val

def destination (out : {p // p ∈ Q} → Fin n) (p : Packet (h := h) D) : Fin n :=
  out p.1

theorem helper_load (a : Helper (h := h) D) :
    Counting.count (helper (h := h) D) a ≤ t := by
  classical
  let f : {p : Packet (h := h) D // helper D p = a} →
      {q // q ∈ D.clusters[a.1]} := fun p =>
    ⟨p.val.1.val, by
      have hp := p.val.2.property
      have he : p.val.2.val = a := p.property
      simpa only [he] using hp⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨q, a'⟩, hp⟩ ⟨⟨q', a''⟩, hp'⟩ he
    have hq : q = q' := by
      apply Subtype.ext
      exact congrArg (fun x : {q // q ∈ D.clusters[a.1]} => x.val) he
    subst q'
    change a'.val = a at hp
    change a''.val = a at hp'
    have ha : a' = a'' := Subtype.ext (hp.trans hp'.symm)
    subst a''
    rfl
  have hc := Counting.count_le_card_of_injective (helper D) a D.clusters[a.1] f hf
  have ht : D.clusters[a.1].card = t :=
    D.cluster_card D.clusters[a.1] (List.getElem_mem a.1.isLt)
  exact hc.trans ht.le

theorem destination_load (out : {p // p ∈ Q} → Fin n) (node : Fin n) :
    Counting.count (destination (h := h) D out) node ≤
      Counting.count out node * h := by
  classical
  let f : {p : Packet (h := h) D // destination D out p = node} →
      {q : {p // p ∈ Q} // out q = node} × Fin h :=
    fun p => (⟨p.val.1, p.property⟩, p.val.2.val.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨q, a⟩, hp⟩ ⟨⟨q', a'⟩, hp'⟩ he
    have hq : q = q' := congrArg (fun x => x.1.val) he
    subst q'
    have hb : a.val.2 = a'.val.2 :=
      congrArg (fun x : {q : {p // p ∈ Q} // out q = node} × Fin h => x.2) he
    have hc : a.val.1 = a'.val.1 :=
      D.unique_cluster_index a.val.1 a'.val.1 q.val a.property a'.property
    have ha : a = a' := Subtype.ext (Prod.ext hc hb)
    subst a'
    rfl
  rw [Counting.count_eq_card_fiber]
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fin,
    ← Counting.count_eq_card_fiber] using hc

theorem physical_source_load (place : Helper (h := h) D → Fin n)
    (hplace : Function.Injective place) (node : Fin n) :
    Counting.count (place ∘ helper (h := h) D) node ≤ t := by
  simp_rw [Counting.count_eq_load]
  apply Counting.load_comp_injective (helper D) (fun _ => 1) place hplace t
  intro a
  rw [← Counting.count_eq_load]
  exact helper_load D a

theorem exists_schedule (place : Helper (h := h) D → Fin n)
    (hplace : Function.Injective place) (out : {p // p ∈ Q} → Fin n)
    (hout : ∀ node, Counting.count out node ≤ d) :
    ∃ slot : Packet (h := h) D → Fin (2 * (t + d * h)),
      Routing.LegalOn Finset.univ (place ∘ helper D) (destination D out) slot := by
  classical
  apply Routing.exists_schedule
  · intro node
    exact (physical_source_load D place hplace node).trans (Nat.le_add_right _ _)
  · intro node
    change Counting.count (destination D out) node ≤ t + d * h
    exact (destination_load D out node).trans
      ((Nat.mul_le_mul_right h (hout node)).trans (Nat.le_add_left _ _))

end SparseMM.PartialDelivery
