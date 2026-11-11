module

public import SparseMM.Model
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM.ExactRouting

open scoped BigOperators

variable {Packet Node : Type*} [DecidableEq Packet] [DecidableEq Node] [Fintype Node]

omit [DecidableEq Packet] [Fintype Node] in
private theorem regular_filter_count (packets : Finset Packet) (f : Packet → Node)
    (D : ℕ) (hregular : ∀ node, (packets.filter (fun p => f p = node)).card = D)
    (nodes : Finset Node) :
    (packets.filter (fun p => f p ∈ nodes)).card = nodes.card * D := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  simp_rw [hregular]
  simp

/-- A positive regular labelled bipartite packet multigraph contains one
packet at every sender and receiver. Hall's condition follows by counting
the actual labelled packets, so parallel edges are retained. -/
theorem exists_perfect_packet_matching (packets : Finset Packet)
    (source destination : Packet → Node) (D : ℕ) (hD : 0 < D)
    (hout : ∀ node, (packets.filter (fun p => source p = node)).card = D)
    (hin : ∀ node, (packets.filter (fun p => destination p = node)).card = D) :
    ∃ matching : Finset Packet, matching ⊆ packets ∧
      (∀ node, (matching.filter (fun p => source p = node)).card = 1) ∧
      (∀ node, (matching.filter (fun p => destination p = node)).card = 1) := by
  classical
  let neighbors : Node → Finset Node := fun node =>
    (packets.filter (fun p => source p = node)).image destination
  have hhall (nodes : Finset Node) : nodes.card ≤ (nodes.biUnion neighbors).card := by
    have hsub : packets.filter (fun p => source p ∈ nodes) ⊆
        packets.filter (fun p => destination p ∈ nodes.biUnion neighbors) := by
      intro p hp
      obtain ⟨hpp, hps⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨hpp, Finset.mem_biUnion.mpr ⟨source p, hps, ?_⟩⟩
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hpp, rfl⟩, rfl⟩
    have hcount := Finset.card_le_card hsub
    rw [regular_filter_count packets source D hout nodes,
      regular_filter_count packets destination D hin (nodes.biUnion neighbors)] at hcount
    exact Nat.le_of_mul_le_mul_right (c := D) (hc := hD) hcount
  obtain ⟨f, hf, hfneighbor⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hhall
  have hp : ∀ node, ∃ p : Packet,
      p ∈ packets ∧ source p = node ∧ destination p = f node := by
    intro node
    obtain ⟨p, hp, hdest⟩ := Finset.mem_image.mp (hfneighbor node)
    obtain ⟨hpackets, hsource⟩ := Finset.mem_filter.mp hp
    exact ⟨p, hpackets, hsource, hdest⟩
  choose chosen hchosen hsource hdestination using hp
  let matching := Finset.univ.image chosen
  have hsub : matching ⊆ packets := by
    intro p hp
    obtain ⟨node, _, rfl⟩ := Finset.mem_image.mp hp
    exact hchosen node
  have hout' (node : Node) : matching.filter (fun p => source p = node) = {chosen node} := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpm, hps⟩ := Finset.mem_filter.mp hp
      obtain ⟨other, _, rfl⟩ := Finset.mem_image.mp hpm
      have he : other = node := (hsource other).symm.trans hps
      simp only [Finset.mem_singleton]
      exact congrArg chosen he
    · intro hp
      have he : p = chosen node := Finset.mem_singleton.mp hp
      subst p
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨node, Finset.mem_univ _, rfl⟩, hsource node⟩
  have hin' (node : Node) : (matching.filter (fun p => destination p = node)).card = 1 := by
    obtain ⟨preimage, hpreimage⟩ := Finite.surjective_of_injective hf node
    have heq : matching.filter (fun p => destination p = node) = {chosen preimage} := by
      ext p
      constructor
      · intro hp
        obtain ⟨hpm, hpd⟩ := Finset.mem_filter.mp hp
        obtain ⟨other, _, rfl⟩ := Finset.mem_image.mp hpm
        have he : f other = f preimage :=
          (hdestination other).symm.trans (hpd.trans hpreimage.symm)
        simp only [Finset.mem_singleton]
        exact congrArg chosen (hf he)
      · intro hp
        have he : p = chosen preimage := Finset.mem_singleton.mp hp
        subst p
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨preimage, Finset.mem_univ _, rfl⟩,
            (hdestination preimage).trans hpreimage⟩
    rw [heq]
    simp
  exact ⟨matching, hsub, fun node => by rw [hout']; simp, hin'⟩

omit [Fintype Node] in
private theorem remove_matching_regular (packets matching : Finset Packet)
    (f : Packet → Node) (D : ℕ) (hsub : matching ⊆ packets)
    (hregular : ∀ node, (packets.filter (fun p => f p = node)).card = D + 1)
    (hmatching : ∀ node, (matching.filter (fun p => f p = node)).card = 1)
    (node : Node) : ((packets \ matching).filter (fun p => f p = node)).card = D := by
  have heq : (packets \ matching).filter (fun p => f p = node) =
      (packets.filter (fun p => f p = node)) \ (matching.filter (fun p => f p = node)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hp, hm⟩, hf⟩
      exact ⟨⟨hp, hf⟩, fun h => hm h.1⟩
    · rintro ⟨⟨hp, hf⟩, hm⟩
      exact ⟨⟨hp, fun h => hm ⟨h, hf⟩⟩, hf⟩
  rw [heq]
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset_filter (fun p => f p = node) hsub)
  rw [hregular node, hmatching node] at hcard
  omega

/-- Exact regular redistribution, with an active finite packet set. Each
induction step removes a perfect labelled-packet matching obtained from Hall. -/
theorem exists_schedule_subset (packets : Finset Packet)
    (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (packets.filter (fun p => source p = node)).card = D)
    (hin : ∀ node, (packets.filter (fun p => destination p = node)).card = D) :
    ∃ slot : {p // p ∈ packets} → Fin D,
      Routing.LegalOn Finset.univ (fun p => source p.val) (fun p => destination p.val) slot := by
  classical
  induction D generalizing packets with
  | zero =>
      have hempty (p : {p // p ∈ packets}) : False := by
        have hp : p.val ∈ packets.filter (fun q => source q = source p.val) :=
          Finset.mem_filter.mpr ⟨p.property, rfl⟩
        have hpos := Finset.card_pos.mpr ⟨p.val, hp⟩
        have hz := hout (source p.val)
        omega
      exact ⟨fun p => (hempty p).elim, fun p _ => (hempty p).elim⟩
  | succ D ih =>
      obtain ⟨matching, hsub, hmout, hmin⟩ :=
        exists_perfect_packet_matching packets source destination (D + 1)
          (Nat.succ_pos D) hout hin
      have hrout := remove_matching_regular packets matching source D hsub hout hmout
      have hrin := remove_matching_regular packets matching destination D hsub hin hmin
      obtain ⟨prior, hprior⟩ := ih (packets \ matching) hrout hrin
      let slot : {p // p ∈ packets} → Fin (D + 1) := fun p =>
        if hp : p.val ∈ matching then ⟨0, Nat.succ_pos D⟩
        else (prior ⟨p.val, Finset.mem_sdiff.mpr ⟨p.property, hp⟩⟩).succ
      have hmatched (p q : Packet) (hp : p ∈ matching) (hq : q ∈ matching)
          (hconflict : source p = source q ∨ destination p = destination q) : p = q := by
        rcases hconflict with hs | hd
        · apply Finset.card_le_one.mp ((hmout (source p)).le)
          · exact Finset.mem_filter.mpr ⟨hp, rfl⟩
          · exact Finset.mem_filter.mpr ⟨hq, hs.symm⟩
        · apply Finset.card_le_one.mp ((hmin (destination p)).le)
          · exact Finset.mem_filter.mpr ⟨hp, rfl⟩
          · exact Finset.mem_filter.mpr ⟨hq, hd.symm⟩
      refine ⟨slot, ?_⟩
      intro p hp q hq hsame hconflict
      apply Subtype.ext
      by_cases hpM : p.val ∈ matching
      · by_cases hqM : q.val ∈ matching
        · exact hmatched p.val q.val hpM hqM hconflict
        · have hv := congrArg Fin.val hsame
          simp [slot, hpM, hqM] at hv
      · by_cases hqM : q.val ∈ matching
        · have hv := congrArg Fin.val hsame
          simp [slot, hpM, hqM] at hv
        · have hs : prior ⟨p.val, Finset.mem_sdiff.mpr ⟨p.property, hpM⟩⟩ =
              prior ⟨q.val, Finset.mem_sdiff.mpr ⟨q.property, hqM⟩⟩ := by
            apply Fin.succ_inj.mp
            simpa only [slot, dite_eq_right hpM, dite_eq_right hqM] using hsame
          exact congrArg (fun r : {p // p ∈ packets \ matching} => r.val)
            (hprior _ (Finset.mem_univ _)
            _ (Finset.mem_univ _) hs hconflict)

/-- Lemma 3 of the supplied paper: a public redistribution with exactly `D`
labelled values at each source and each destination has a legal schedule of
exactly `D` slots. Self-destined packets can subsequently be kept local. -/
theorem exists_schedule [Fintype Packet] (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card = D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card = D) :
    ∃ slot : Packet → Fin D, Routing.LegalOn Finset.univ source destination slot := by
  classical
  obtain ⟨schedule, hschedule⟩ := exists_schedule_subset Finset.univ source destination D hout hin
  refine ⟨fun p => schedule ⟨p, Finset.mem_univ _⟩, ?_⟩
  intro p hp q hq hsame hconflict
  exact congrArg Subtype.val (hschedule _ (Finset.mem_univ _) _ (Finset.mem_univ _)
    hsame hconflict)

/-- The exact `D`-slot schedule actually delivers arbitrary source-local
values through the local send/receive execution semantics. All public code is
chosen before numerical values. -/
theorem exists_public_redistribution [Fintype Packet] {Value : Type*}
    (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card = D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card = D) :
    ∃ plan : Model.StaticPlan source destination D,
      ∀ (values : Packet → Value) (p : Packet),
        Model.execute plan values D (destination p) p = some (values p) := by
  classical
  obtain ⟨slot, hslot⟩ := exists_schedule source destination D hout hin
  exact ⟨⟨slot, hslot⟩, fun values p => Model.execute_delivers _ values p⟩

end SparseMM.ExactRouting
