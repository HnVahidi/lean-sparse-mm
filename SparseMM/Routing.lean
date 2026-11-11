module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.ByContra

@[expose] public section

/-!
# Static routing of labelled packets

Packets are separate objects even when their source and destination agree.
The greedy construction gives at most twice the maximum per-node load
rounds. In each round every node sends at most one packet and receives at
most one packet. The schedule depends only on known ownership maps. A packet
whose source equals its destination is already available locally and may be
omitted from network traffic; removing it preserves both capacity bounds.
-/

namespace SparseMM.Routing

/-- A slot assignment obeys both directed port constraints. -/
def LegalOn {Packet Node : Type*} {rounds : ℕ}
    (packets : Finset Packet) (source destination : Packet → Node)
    (slot : Packet → Fin rounds) : Prop :=
  ∀ p ∈ packets, ∀ q ∈ packets, slot p = slot q →
    (source p = source q ∨ destination p = destination q) → p = q

private theorem schedule_subset
    {Packet Node : Type*} [DecidableEq Packet] [DecidableEq Node]
    (packets : Finset Packet) (source destination : Packet → Node)
    (D : ℕ) (hD : 0 < D)
    (hout : ∀ node, (packets.filter (fun p => source p = node)).card ≤ D)
    (hin : ∀ node, (packets.filter (fun p => destination p = node)).card ≤ D) :
    ∃ slot : Packet → Fin (2 * D), LegalOn packets source destination slot := by
  classical
  induction packets using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => ⟨0, by omega⟩, by simp [LegalOn]⟩
  | @insert e packets he ih =>
      have ho (node) : (packets.filter (fun p => source p = node)).card ≤ D := by
        exact (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.subset_insert e packets))).trans (hout node)
      have hi (node) : (packets.filter (fun p => destination p = node)).card ≤ D := by
        exact (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.subset_insert e packets))).trans (hin node)
      obtain ⟨slot, hslot⟩ := ih ho hi
      let out := packets.filter (fun p => source p = source e)
      let incoming := packets.filter (fun p => destination p = destination e)
      have houtsmall : out.card < D := by
        have h := hout (source e)
        simp only [Finset.filter_insert] at h
        have hnot : e ∉ out := fun hm => he (Finset.mem_filter.mp hm).1
        change (insert e out).card ≤ D at h
        rw [Finset.card_insert_of_notMem hnot] at h
        omega
      have hinsmall : incoming.card < D := by
        have h := hin (destination e)
        simp only [Finset.filter_insert] at h
        have hnot : e ∉ incoming := fun hm => he (Finset.mem_filter.mp hm).1
        change (insert e incoming).card ≤ D at h
        rw [Finset.card_insert_of_notMem hnot] at h
        omega
      let blocked := (out.image slot) ∪ (incoming.image slot)
      have hblocked : blocked.card < (Finset.univ : Finset (Fin (2*D))).card := by
        have hu := Finset.card_union_le (out.image slot) (incoming.image slot)
        have ho' := Finset.card_image_le (s := out) (f := slot)
        have hi' := Finset.card_image_le (s := incoming) (f := slot)
        simp only [Finset.card_univ, Fintype.card_fin]
        dsimp [blocked]
        omega
      obtain ⟨fresh, _hfresh, hfresh⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hblocked
      have hdifferent (p) (hp : p ∈ packets)
          (hconflict : source p = source e ∨ destination p = destination e) :
          slot p ≠ fresh := by
        intro hsame
        apply hfresh
        change fresh ∈ out.image slot ∪ incoming.image slot
        rw [← hsame]
        rcases hconflict with ho' | hi'
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, ho'⟩, rfl⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hi'⟩, rfl⟩)
      let extended := fun p => if p = e then fresh else slot p
      refine ⟨extended, ?_⟩
      intro p hp q hq hsame hconflict
      by_cases hpe : p = e
      · by_cases hqe : q = e
        · exact hpe.trans hqe.symm
        · have hq' := (Finset.mem_insert.mp hq).resolve_left hqe
          have hconflict' : source q = source e ∨ destination q = destination e :=
            hconflict.elim
              (fun h => Or.inl (h.symm.trans (congrArg source hpe)))
              (fun h => Or.inr (h.symm.trans (congrArg destination hpe)))
          have hsf : fresh = slot q := by simpa [extended, hpe, hqe] using hsame
          exact False.elim (hdifferent q hq' hconflict' hsf.symm)
      · have hp' := (Finset.mem_insert.mp hp).resolve_left hpe
        by_cases hqe : q = e
        · have hconflict' : source p = source e ∨ destination p = destination e := by
            simpa only [hqe] using hconflict
          have hsf : slot p = fresh := by simpa [extended, hpe, hqe] using hsame
          exact False.elim (hdifferent p hp' hconflict' hsf)
        · have hq' := (Finset.mem_insert.mp hq).resolve_left hqe
          apply hslot p hp' q hq' _ hconflict
          simpa [extended, hpe, hqe] using hsame

/-- Every finite packet multiset whose source and destination loads are at
most D has a static legal schedule of length 2D. Packet labels distinguish
parallel edges, so this is not restricted to simple communication graphs. -/
theorem exists_schedule
    {Packet Node : Type*} [Fintype Packet] [DecidableEq Node]
    (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card ≤ D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card ≤ D) :
    ∃ slot : Packet → Fin (2 * D), LegalOn Finset.univ source destination slot := by
  classical
  by_cases hD : 0 < D
  · exact schedule_subset Finset.univ source destination D hD hout hin
  · have hzero : D = 0 := by omega
    have impossible (p : Packet) : False := by
      have hp : p ∈ Finset.univ.filter (fun q => source q = source p) := by simp
      have hpos := Finset.card_pos.mpr ⟨p, hp⟩
      have h := hout (source p)
      omega
    exact ⟨fun p => (impossible p).elim, fun p _ => (impossible p).elim⟩

/-- A concrete scheduled round contains at most one packet from each source. -/
theorem send_capacity
    {Packet Node : Type*} [Fintype Packet] [DecidableEq Node]
    {rounds : ℕ} (source destination : Packet → Node) (slot : Packet → Fin rounds)
    (hlegal : LegalOn Finset.univ source destination slot)
    (time : Fin rounds) (node : Node) :
    (Finset.univ.filter (fun p => slot p = time ∧ source p = node)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨_, hpt, hps⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hqt, hqs⟩ := Finset.mem_filter.mp hq
  exact hlegal p (Finset.mem_univ _) q (Finset.mem_univ _)
    (hpt.trans hqt.symm) (Or.inl (hps.trans hqs.symm))

/-- A concrete scheduled round contains at most one packet at each destination. -/
theorem receive_capacity
    {Packet Node : Type*} [Fintype Packet] [DecidableEq Node]
    {rounds : ℕ} (source destination : Packet → Node) (slot : Packet → Fin rounds)
    (hlegal : LegalOn Finset.univ source destination slot)
    (time : Fin rounds) (node : Node) :
    (Finset.univ.filter (fun p => slot p = time ∧ destination p = node)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨_, hpt, hpd⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hqt, hqd⟩ := Finset.mem_filter.mp hq
  exact hlegal p (Finset.mem_univ _) q (Finset.mem_univ _)
    (hpt.trans hqt.symm) (Or.inr (hpd.trans hqd.symm))

/-- Every labelled packet occurs at its destination at exactly its assigned
time. Combined with the two capacity theorems, this makes the slot assignment
a complete delivery plan rather than only a count of possible rounds. -/
theorem packet_delivery_iff
    {Packet Node : Type*} [Fintype Packet] [DecidableEq Node]
    {rounds : ℕ} (destination : Packet → Node) (slot : Packet → Fin rounds)
    (p : Packet) (time : Fin rounds) (node : Node) :
    p ∈ Finset.univ.filter (fun q => slot q = time ∧ destination q = node) ↔
      slot p = time ∧ destination p = node := by
  simp

end SparseMM.Routing
