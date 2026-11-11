module

public import SparseMM.Balancing
public import SparseMM.Counting
public import SparseMM.OutputAssignment
public import SparseMM.Routing

@[expose] public section

/-!
# Two-stage public multicast schedules

Every request is a separately labelled occurrence of an input entry. A
broadcaster first receives one copy of every needed input assigned to it, then
sends one copy for every request. The theorem bounds both directed port loads
and constructs legal schedules for both phases. Numerical values are not part
of the scheduling claim.
-/

open scoped BigOperators

namespace SparseMM.Multicast

/-- An input is needed precisely when it occurs in at least one request. -/
abbrev Needed {Input Request : Type*} [Fintype Request] [DecidableEq Input]
    (entry : Request → Input) := {e : Input // 0 < Counting.count entry e}

/-- Every actual request supplies its own witness that its entry is needed. -/
theorem request_needed {Input Request : Type*} [Fintype Request] [DecidableEq Input]
    (entry : Request → Input) (request : Request) :
    0 < Counting.count entry (entry request) := by
  classical
  exact Finset.card_pos.mpr ⟨request, by simp⟩

/-- Composition counts each input once for every labelled request of that
input. Parallel requests remain distinct occurrences. -/
theorem count_comp_eq_load {Input Request Node : Type*} [Fintype Input]
    [Fintype Request] [DecidableEq Input] [DecidableEq Node]
    (entry : Request → Input) (broadcaster : Input → Node) (node : Node) :
    Counting.count (broadcaster ∘ entry) node =
      Counting.load broadcaster (fun e => Counting.count entry e) node := by
  classical
  simp only [Counting.count_eq_load, Counting.load]
  symm
  calc
    (∑ e : Input, if broadcaster e = node then
        (∑ r : Request, if entry r = e then 1 else 0) else 0) =
      ∑ e : Input, ∑ r : Request,
        if entry r = e then (if broadcaster e = node then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases h : broadcaster e = node <;> simp [h]
    _ = ∑ r : Request, ∑ e : Input,
        if entry r = e then (if broadcaster e = node then 1 else 0) else 0 := Finset.sum_comm
    _ = ∑ r : Request, if (broadcaster ∘ entry) r = node then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp

/-- Generic finite jobs may be balanced by enumerating them with `equivFin`.
This changes neither weights nor the actual per-machine sum. -/
theorem exists_balanced_broadcaster {Input : Type*} [Fintype Input]
    (n B W : ℕ) (hn : 0 < n) (weight : Input → ℕ)
    (hitem : ∀ e, weight e ≤ W) (htotal : (∑ e : Input, weight e) ≤ n * B) :
    ∃ broadcaster : Input → Fin n,
      ∀ node, Counting.load broadcaster weight node ≤ B + W := by
  classical
  let enumeration := Fintype.equivFin Input
  obtain ⟨assignment, hbound⟩ := Balancing.exists_assignment_le_average_add n
    (Fintype.card Input) B W hn (fun t => weight (enumeration.symm t))
    (fun t => hitem (enumeration.symm t)) (by
      simpa only [enumeration.symm.sum_comp] using htotal)
  refine ⟨fun e => assignment (enumeration e), fun node => ?_⟩
  have hsum : Counting.load (fun e => assignment (enumeration e)) weight node =
      Balancing.binLoad (fun t => weight (enumeration.symm t)) assignment node := by
    unfold Counting.load Balancing.binLoad
    simpa only [Equiv.apply_symm_apply] using
      (enumeration.symm.sum_comp (fun e => if assignment (enumeration e) = node then weight e else 0)).symm
  rw [hsum]
  exact hbound node

/-- Dropping unused inputs can only reduce an original holder's send count. -/
theorem needed_original_count_le {Input Request Node : Type*} [Fintype Input]
    [Fintype Request] [DecidableEq Input] [DecidableEq Node]
    (entry : Request → Input) (original : Input → Node) (node : Node) :
    Counting.count (fun e : Needed entry => original e.val) node ≤ Counting.count original node := by
  classical
  rw [Counting.count_eq_card_fiber, Counting.count_eq_card_fiber]
  apply Fintype.card_le_of_injective
    (fun e : {e : Needed entry // original e.val = node} =>
      (⟨e.val.val, e.property⟩ : {e : Input // original e = node}))
  intro a b h
  have he : a.val.val = b.val.val :=
    congrArg (fun e : {e : Input // original e = node} => e.val) h
  exact Subtype.ext (Subtype.ext he)

/-- Every received first-stage input costs at least one second-stage copy.
Unused inputs have no first-stage packet. -/
theorem needed_broadcaster_count_le_load {Input Request : Type*} [Fintype Input]
    [Fintype Request] [DecidableEq Input] {n : ℕ}
    (entry : Request → Input) (broadcaster : Input → Fin n) (node : Fin n) :
    Counting.count (fun e : Needed entry => broadcaster e.val) node ≤
      Counting.load broadcaster (fun e => Counting.count entry e) node := by
  classical
  calc
    _ ≤ Counting.load (fun e : Needed entry => broadcaster e.val)
        (fun e => Counting.count entry e.val) node :=
      Counting.count_le_load _ _ (fun e => e.property) node
    _ ≤ Counting.load broadcaster (fun e => Counting.count entry e) node := by
      exact OutputAssignment.sum_along_embedding_le
        (⟨Subtype.val, Subtype.val_injective⟩ : Needed entry ↪ Input)
        (fun e => if broadcaster e = node then Counting.count entry e else 0)

/-- Construct broadcasters and prove every send/receive count in both phases.
The first phase sends one packet per needed input, and the second phase sends
one packet per labelled request. -/
theorem exists_two_stage_loads {Input Request : Type*} [Fintype Input]
    [Fintype Request] [DecidableEq Input]
    (n K L W : ℕ) (hn : 0 < n)
    (entry : Request → Input) (target : Request → Fin n) (original : Input → Fin n)
    (hfanout : ∀ e, Counting.count entry e ≤ W)
    (hreceiver : ∀ node, Counting.count target node ≤ L)
    (horiginal : ∀ node, Counting.count original node ≤ K) :
    ∃ broadcaster : Input → Fin n,
      (∀ node, Counting.load broadcaster (fun e => Counting.count entry e) node ≤ L + W) ∧
      (∀ node, Counting.count (fun e : Needed entry => original e.val) node ≤ K) ∧
      (∀ node, Counting.count (fun e : Needed entry => broadcaster e.val) node ≤ L + W) ∧
      (∀ node, Counting.count (broadcaster ∘ entry) node ≤ L + W) := by
  classical
  have htotal : (∑ e : Input, Counting.count entry e) ≤ n * L := by
    rw [Counting.sum_count, ← Counting.sum_count target]
    calc
      (∑ node : Fin n, Counting.count target node) ≤ ∑ _node : Fin n, L :=
        Finset.sum_le_sum (fun node _ => hreceiver node)
      _ = n * L := by simp
  obtain ⟨broadcaster, hload⟩ := exists_balanced_broadcaster n L W hn
    (fun e => Counting.count entry e) hfanout htotal
  refine ⟨broadcaster, hload, ?_, ?_, ?_⟩
  · intro node
    exact (needed_original_count_le entry original node).trans (horiginal node)
  · intro node
    exact (needed_broadcaster_count_le_load entry broadcaster node).trans (hload node)
  · intro node
    rw [count_comp_eq_load]
    exact hload node

/-- Both public stages admit actual port-legal schedules. The first costs at
most `2 * max K (L+W)` rounds and the second at most `2 * (L+W)` rounds. -/
theorem exists_two_stage_schedules {Input Request : Type*} [Fintype Input]
    [Fintype Request] [DecidableEq Input]
    (n K L W : ℕ) (hn : 0 < n)
    (entry : Request → Input) (target : Request → Fin n) (original : Input → Fin n)
    (hfanout : ∀ e, Counting.count entry e ≤ W)
    (hreceiver : ∀ node, Counting.count target node ≤ L)
    (horiginal : ∀ node, Counting.count original node ≤ K) :
    ∃ broadcaster : Input → Fin n,
      (∃ first : Needed entry → Fin (2 * max K (L + W)),
        Routing.LegalOn Finset.univ (fun e => original e.val)
          (fun e => broadcaster e.val) first) ∧
      (∃ second : Request → Fin (2 * (L + W)),
        Routing.LegalOn Finset.univ (broadcaster ∘ entry) target second) := by
  classical
  obtain ⟨broadcaster, _hload, hfirstout, hfirstin, hsecondout⟩ :=
    exists_two_stage_loads n K L W hn entry target original hfanout hreceiver horiginal
  refine ⟨broadcaster, ?_, ?_⟩
  · apply Routing.exists_schedule _ _ (max K (L + W))
    · intro node
      exact (hfirstout node).trans (Nat.le_max_left _ _)
    · intro node
      exact (hfirstin node).trans (Nat.le_max_right _ _)
  · apply Routing.exists_schedule _ _ (L + W) hsecondout
    intro node
    exact (hreceiver node).trans (Nat.le_add_right _ _)

end SparseMM.Multicast
