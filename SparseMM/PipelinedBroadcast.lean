module

public import SparseMM.Model
public import SparseMM.BroadcastLower
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace SparseMM.PipelinedBroadcast

abbrev Child (n : ℕ) := {v : Fin n // 0 < v.val}
abbrev Packet (n k : ℕ) := Fin k × Child n

def level (v : ℕ) : ℕ := Nat.log 2 (v + 1)

def parent {n : ℕ} (v : Child n) : Fin n :=
  ⟨(v.val.val - 1) / 2, by have := v.property; have := v.val.isLt; omega⟩

def parity {n : ℕ} (v : Child n) : ℕ := (v.val.val - 1) % 2

theorem parent_lt {n : ℕ} (v : Child n) : (parent v).val < v.val.val := by
  have := v.property
  simp only [parent]
  omega

theorem parent_ne_child {n : ℕ} (v : Child n) : parent v ≠ v.val := by
  intro heq
  have := parent_lt v
  have := congrArg Fin.val heq
  omega

theorem level_parent {n : ℕ} (v : Child n) : level (parent v).val + 1 = level v.val.val := by
  have htwo : 2 ≤ v.val.val + 1 := by have := v.property; omega
  have hdiv : (v.val.val - 1) / 2 + 1 = (v.val.val + 1) / 2 := by
    have := v.property
    omega
  unfold level parent
  rw [Nat.log_of_one_lt_of_le (by decide) htwo]
  rw [hdiv]

theorem level_le_clog {n : ℕ} (v : Fin n) : level v.val ≤ Nat.clog 2 n := by
  exact (Nat.log_mono_right (by have := v.isLt; omega)).trans (Nat.log_le_clog 2 n)

theorem child_ext {n : ℕ} (a b : Child n)
    (hp : parent a = parent b) (hc : parity a = parity b) : a = b := by
  apply Subtype.ext
  apply Fin.ext
  have hp' := congrArg Fin.val hp
  have ha := a.property
  have hb := b.property
  change (a.val.val - 1) / 2 = (b.val.val - 1) / 2 at hp'
  unfold parity at hc
  omega

def rounds (n k : ℕ) : ℕ := 2 * k + 2 * Nat.clog 2 n

def time {n k : ℕ} (p : Packet n k) : ℕ :=
  2 * p.1.val + 2 * level (parent p.2).val + parity p.2

theorem time_lt_rounds {n k : ℕ} (p : Packet n k) : time p < rounds n k := by
  have hr := p.1.isLt
  have hp := level_parent p.2
  have hd := level_le_clog p.2.val
  have hpar : parity p.2 < 2 := Nat.mod_lt _ (by decide)
  unfold time rounds
  omega

def source {n k : ℕ} (p : Packet n k) : Fin n := parent p.2
def destination {n k : ℕ} (p : Packet n k) : Fin n := p.2.val

def slot {n k : ℕ} (p : Packet n k) : Fin (rounds n k) := ⟨time p, time_lt_rounds p⟩

theorem legal {n k : ℕ} : Routing.LegalOn Finset.univ
    (source (n := n) (k := k)) destination slot := by
  intro p _ q _ ht hconflict
  have ht' := congrArg Fin.val ht
  change time p = time q at ht'
  have hpp : parity p.2 < 2 := Nat.mod_lt _ (by decide)
  have hqp : parity q.2 < 2 := Nat.mod_lt _ (by decide)
  rcases hconflict with hs | hd
  · have hlev : level (parent p.2).val = level (parent q.2).val := congrArg (level ∘ Fin.val) hs
    have hr : p.1 = q.1 := by
      apply Fin.ext
      unfold time at ht'
      omega
    have hpar : parity p.2 = parity q.2 := by
      unfold time at ht'
      rw [hr, hlev] at ht'
      omega
    exact Prod.ext hr (child_ext p.2 q.2 hs hpar)
  · have hc : p.2 = q.2 := Subtype.ext hd
    have hr : p.1 = q.1 := by
      apply Fin.ext
      unfold time at ht'
      rw [hc] at ht'
      omega
    exact Prod.ext hr hc

def plan (n k : ℕ) : Model.StaticPlan (source (n := n) (k := k)) destination (rounds n k) :=
  ⟨slot, legal⟩

theorem parent_before {n k : ℕ} (p : Packet n k) (hp : 0 < (parent p.2).val) :
    time (p.1, (⟨parent p.2, hp⟩ : Child n)) < time p := by
  have hlevel := level_parent (⟨parent p.2, hp⟩ : Child n)
  have hpar : parity (⟨parent p.2, hp⟩ : Child n) < 2 := Nat.mod_lt _ (by decide)
  unfold time
  dsimp only at hlevel ⊢
  omega

section Execution

variable {n k : ℕ} {Value : Type*}

abbrev State (n k : ℕ) (Value : Type*) := Fin n → Fin k → Option Value

def root (hn : 0 < n) : Fin n := ⟨0, hn⟩

/-- Only the root initially knows the `k` private messages. -/
def initial (hn : 0 < n) (values : Fin k → Value) : State n k Value :=
  fun node r => if node = root hn then some (values r) else none

/-- Each selected edge reads its message coordinate from the sender's own
memory. This projection is local; it does not supply missing remote values. -/
def packetState (state : State n k Value) : Model.Configuration (Packet n k) (Fin n) Value :=
  fun node p => state node p.1

def accept (memory : Fin k → Option Value) (message : Option (Packet n k × Value)) :
    Fin k → Option Value :=
  fun r => match message with
    | none => memory r
    | some (p, value) => if r = p.1 then some value else memory r

noncomputable section

/-- One relay round: the verified network selects one actual outgoing message,
then the receiver stores its value under that message's public coordinate. -/
def step (round : ℕ) (state : State n k Value) : State n k Value :=
  fun node => accept (state node)
    (Model.receive (plan n k) round node (packetState state))

def execute (hn : 0 < n) (values : Fin k → Value) : ℕ → State n k Value
  | 0 => initial hn values
  | round + 1 => step round (execute hn values round)

def Sound (values : Fin k → Value) (state : State n k Value) : Prop :=
  ∀ node r, state node r = none ∨ state node r = some (values r)

theorem receive_sound (values : Fin k → Value) (state : State n k Value)
    (hsound : Sound values state) (round : ℕ) (node : Fin n)
    (p : Packet n k) (value : Value)
    (hreceive : Model.receive (plan n k) round node (packetState state) = some (p, value)) :
    value = values p.1 := by
  have hsend := (Model.receive_spec (plan n k) round node (packetState state) p value hreceive).2.2.2
  have hsource := (Model.send_spec (plan n k) round (source p)
    (packetState state (source p)) p value hsend).2
  change state (source p) p.1 = some value at hsource
  rcases hsound (source p) p.1 with hnone | hsome
  · rw [hnone] at hsource
    contradiction
  · exact Option.some.inj (hsource.symm.trans hsome)

theorem step_sound (values : Fin k → Value) (state : State n k Value)
    (hsound : Sound values state) (round : ℕ) : Sound values (step round state) := by
  intro node r
  cases hr : Model.receive (plan n k) round node (packetState state) with
  | none => simpa only [step, hr, accept] using hsound node r
  | some message =>
      obtain ⟨p, value⟩ := message
      have hv := receive_sound values state hsound round node p value hr
      by_cases heq : r = p.1
      · right
        simp [step, hr, accept, heq, hv]
      · simpa only [step, hr, accept, ite_eq_right heq] using hsound node r

theorem step_preserves (values : Fin k → Value) (state : State n k Value)
    (hsound : Sound values state) (round : ℕ) (node : Fin n) (r : Fin k)
    (hknown : state node r = some (values r)) :
    step round state node r = some (values r) := by
  cases hr : Model.receive (plan n k) round node (packetState state) with
  | none => simpa only [step, hr, accept] using hknown
  | some message =>
      obtain ⟨p, value⟩ := message
      have hv := receive_sound values state hsound round node p value hr
      by_cases heq : r = p.1
      · simp [step, hr, accept, heq, hv]
      · simpa only [step, hr, accept, ite_eq_right heq] using hknown

theorem receive_at_time (state : State n k Value) (p : Packet n k) (value : Value)
    (hsource : state (source p) p.1 = some value) :
    Model.receive (plan n k) (time p) (destination p) (packetState state) = some (p, value) := by
  have hsne : source p ≠ destination p := parent_ne_child p.2
  have hi := Model.incomingLabel_eq_some (plan n k) (time p) (destination p) p rfl rfl hsne
  have ho := Model.outgoingLabel_eq_some (plan n k) (time p) (source p) p rfl rfl (Ne.symm hsne)
  simp only [Model.receive, hi, Option.bind_some, Model.send, ho, packetState,
    hsource, Option.map_some]

theorem step_at_time (state : State n k Value) (p : Packet n k) (value : Value)
    (hsource : state (source p) p.1 = some value) :
    step (time p) state (destination p) p.1 = some value := by
  simp [step, receive_at_time state p value hsource, accept]

/-- Every present value is correct; the root retains all messages; and each
scheduled child has its message immediately after that packet's assigned slot. -/
theorem execution_invariant (hn : 0 < n) (values : Fin k → Value) (round : ℕ) :
    Sound values (execute hn values round) ∧
    (∀ r, execute hn values round (root hn) r = some (values r)) ∧
    (∀ p : Packet n k, time p < round →
      execute hn values round (destination p) p.1 = some (values p.1)) := by
  induction round with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro node r
        by_cases hnode : node = root hn
        · right; simp [execute, initial, hnode]
        · left; simp [execute, initial, hnode]
      · intro r
        simp [execute, initial]
      · intro p hp
        omega
  | succ round ih =>
      refine ⟨step_sound values _ ih.1 round, ?_, ?_⟩
      · intro r
        exact step_preserves values _ ih.1 round (root hn) r (ih.2.1 r)
      · intro p hp
        by_cases hprev : time p < round
        · exact step_preserves values _ ih.1 round (destination p) p.1 (ih.2.2 p hprev)
        · have hnow : time p = round := by omega
          have hsource : execute hn values round (source p) p.1 = some (values p.1) := by
            by_cases hroot : source p = root hn
            · rw [hroot]
              exact ih.2.1 p.1
            · have hpos : 0 < (parent p.2).val := by
                by_contra hnonpos
                apply hroot
                apply Fin.ext
                change (parent p.2).val = 0
                omega
              let prior : Packet n k := (p.1, ⟨parent p.2, hpos⟩)
              have hbefore : time prior < round := by
                have hb := parent_before p hpos
                change time prior < time p at hb
                omega
              exact ih.2.2 prior hbefore
          change step round _ _ _ = _
          simpa only [hnow] using step_at_time _ p _ hsource

/-- All `k` private source messages reach every machine after the explicit
`2*k + 2*ceil(log₂ n)` round budget. The public code is independent of values. -/
theorem broadcasts (hn : 0 < n) (values : Fin k → Value) (node : Fin n) (r : Fin k) :
    execute hn values (rounds n k) node r = some (values r) := by
  have hinvariant := execution_invariant hn values (rounds n k)
  by_cases hroot : node = root hn
  · rw [hroot]
    exact hinvariant.2.1 r
  · have hpos : 0 < node.val := by
      by_contra hnonpos
      apply hroot
      apply Fin.ext
      change node.val = 0
      omega
    exact hinvariant.2.2 (r, ⟨node, hpos⟩) (time_lt_rounds _)

/-- Capacity holds on every relay state, independently of numerical data and
whether any source value is missing. -/
theorem port_capacity (state : State n k Value) (round : ℕ) (node : Fin n) :
    ((Model.transmitted (plan n k) round (packetState state)).filter
      (fun p => source p = node)).card ≤ 1 ∧
    ((Model.transmitted (plan n k) round (packetState state)).filter
      (fun p => destination p = node)).card ≤ 1 :=
  ⟨Model.actual_send_capacity _ _ _ _, Model.actual_receive_capacity _ _ _ _⟩

end
end Execution

end SparseMM.PipelinedBroadcast

namespace SparseMM.PipelinedAggregation

open scoped BigOperators
open PipelinedBroadcast (Packet Child parent level parity rounds root)

def source {n k : ℕ} (p : Packet n k) : Fin n := p.2.val
def destination {n k : ℕ} (p : Packet n k) : Fin n := parent p.2
def time {n k : ℕ} (p : Packet n k) : ℕ := rounds n k - 1 - PipelinedBroadcast.time p

theorem time_lt_rounds {n k : ℕ} (p : Packet n k) : time p < rounds n k := by
  have := PipelinedBroadcast.time_lt_rounds p
  unfold time
  omega

def slot {n k : ℕ} (p : Packet n k) : Fin (rounds n k) := ⟨time p, time_lt_rounds p⟩

theorem legal {n k : ℕ} : Routing.LegalOn Finset.univ
    (source (n := n) (k := k)) destination slot := by
  intro p hp q hq ht hc
  have ht' := congrArg Fin.val ht
  change time p = time q at ht'
  have hp' := PipelinedBroadcast.time_lt_rounds p
  have hq' := PipelinedBroadcast.time_lt_rounds q
  have htime : PipelinedBroadcast.slot p = PipelinedBroadcast.slot q := by
    apply Fin.ext
    change PipelinedBroadcast.time p = PipelinedBroadcast.time q
    unfold time at ht'
    omega
  apply PipelinedBroadcast.legal p hp q hq htime
  exact hc.elim Or.inr Or.inl

def plan (n k : ℕ) : Model.StaticPlan (source (n := n) (k := k)) destination (rounds n k) :=
  ⟨slot, legal⟩

theorem source_ne_destination {n k : ℕ} (p : Packet n k) : source p ≠ destination p :=
  Ne.symm (PipelinedBroadcast.parent_ne_child p.2)

theorem child_before {n k : ℕ} (p : Packet n k) (hp : 0 < (parent p.2).val) :
    time p < time (p.1, (⟨parent p.2, hp⟩ : Child n)) := by
  have hbefore := PipelinedBroadcast.parent_before p hp
  have hpbound := PipelinedBroadcast.time_lt_rounds p
  have hparentbound := PipelinedBroadcast.time_lt_rounds (p.1, (⟨parent p.2, hp⟩ : Child n))
  unfold time
  omega

section Execution

variable {n k : ℕ} {S : Type*} [AddCommMonoid S]

abbrev State (n k : ℕ) (S : Type*) := Fin n → Fin k → S

/-- Every node initially holds its own private aggregation inputs. -/
def initial (values : Fin n → Fin k → S) : State n k S := values

def packetState (state : State n k S) : Model.Configuration (Packet n k) (Fin n) S :=
  fun node p => some (state node p.1)

/-- A node clears a coordinate precisely when it sends that accumulated
coordinate to its parent. The decision is public and reads no remote data. -/
def retained (round : ℕ) (state : State n k S) (node : Fin n) (r : Fin k) : S :=
  if ∃ p : Packet n k, time p = round ∧ source p = node ∧ p.1 = r then 0
  else state node r

noncomputable section

/-- A receiver adds only the value of its actual received message to that
message's coordinate. Other coordinates receive the additive identity. -/
def received (round : ℕ) (state : State n k S) (node : Fin n) (r : Fin k) : S :=
  match Model.receive (plan n k) round node (packetState state) with
  | none => 0
  | some (p, value) => if p.1 = r then value else 0

def step (round : ℕ) (state : State n k S) : State n k S :=
  fun node r => retained round state node r + received round state node r

def execute (values : Fin n → Fin k → S) : ℕ → State n k S
  | 0 => initial values
  | round + 1 => step round (execute values round)

/-- Auxiliary mathematical accounting of values sent in a round. The actual
local code above uses its own accumulator and one received message. -/
def outMass (round : ℕ) (state : State n k S) (r : Fin k) (node : Fin n) : S :=
  ∑ p : Packet n k, if time p = round ∧ p.1 = r then
    if source p = node then state (source p) r else 0 else 0

def inMass (round : ℕ) (state : State n k S) (r : Fin k) (node : Fin n) : S :=
  ∑ p : Packet n k, if time p = round ∧ p.1 = r then
    if destination p = node then state (source p) r else 0 else 0

theorem total_inMass_eq_outMass (round : ℕ) (state : State n k S) (r : Fin k) :
    (∑ node, inMass round state r node) = ∑ node, outMass round state r node := by
  unfold inMass outMass
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : time p = round ∧ p.1 = r <;> simp [h]

theorem retained_add_outMass (round : ℕ) (state : State n k S) (node : Fin n) (r : Fin k) :
    retained round state node r + outMass round state r node = state node r := by
  unfold retained
  split_ifs with hex
  · obtain ⟨p, ht, hs, hr⟩ := hex
    rw [zero_add]
    unfold outMass
    rw [Finset.sum_eq_single p]
    · simp [ht, hs, hr]
    · intro q _ hne
      by_cases hqt : time q = round ∧ q.1 = r
      · by_cases hqs : source q = node
        · have hqp : q = p := legal q (Finset.mem_univ _) p (Finset.mem_univ _)
            (Fin.ext (hqt.1.trans ht.symm)) (Or.inl (hqs.trans hs.symm))
          exact (hne hqp).elim
        · simp [hqt, hqs]
      · simp [hqt]
    · simp
  · have hzero : outMass round state r node = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      by_cases hpt : time p = round ∧ p.1 = r
      · have hps : source p ≠ node := by
          intro hs
          exact hex ⟨p, hpt.1, hs, hpt.2⟩
        simp [hpt, hps]
      · simp [hpt]
    rw [hzero, add_zero]

theorem received_eq_inMass (round : ℕ) (state : State n k S) (node : Fin n) (r : Fin k) :
    received round state node r = inMass round state r node := by
  cases hi : Model.incomingLabel (plan n k) round node with
  | none =>
      have hzero : inMass round state r node = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        by_cases hpt : time p = round ∧ p.1 = r
        · have hpd : destination p ≠ node := by
            intro hd
            have hsne : source p ≠ node := by
              rw [← hd]
              exact source_ne_destination p
            have heq := Model.incomingLabel_eq_some (plan n k) round node p hpt.1 hd hsne
            rw [hi] at heq
            contradiction
          simp [hpt, hpd]
        · simp [hpt]
      simp [received, Model.receive, hi, hzero]
  | some p =>
      obtain ⟨ht, hd, hs⟩ := Model.incomingLabel_spec (plan n k) round node p hi
      change time p = round at ht
      have ho := Model.outgoingLabel_eq_some (plan n k) round (source p) p ht rfl
        (Ne.symm (source_ne_destination p))
      have hreceive : Model.receive (plan n k) round node (packetState state) =
          some (p, state (source p) p.1) := by
        simp [Model.receive, hi, Model.send, ho, packetState]
      unfold received
      rw [hreceive]
      unfold inMass
      rw [Finset.sum_eq_single p]
      · change (if p.1 = r then state (source p) p.1 else 0) = _
        by_cases hr : p.1 = r <;> simp [hr, ht, hd]
      · intro q _ hne
        by_cases hqt : time q = round ∧ q.1 = r
        · by_cases hqd : destination q = node
          · have hqp : q = p := legal q (Finset.mem_univ _) p (Finset.mem_univ _)
              (Fin.ext (hqt.1.trans ht.symm)) (Or.inr (hqd.trans hd.symm))
            exact (hne hqp).elim
          · simp [hqt, hqd]
        · simp [hqt]
      · simp

/-- Every round preserves the total of each coordinate. Clearing a sent
accumulator and adding its received value avoids duplicate counting. -/
theorem step_conserves (round : ℕ) (state : State n k S) (r : Fin k) :
    (∑ node, step round state node r) = ∑ node, state node r := by
  simp only [step, Finset.sum_add_distrib, received_eq_inMass]
  rw [total_inMass_eq_outMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro node _
  exact retained_add_outMass round state node r

theorem execute_conserves (values : Fin n → Fin k → S) (round : ℕ) (r : Fin k) :
    (∑ node, execute values round node r) = ∑ node, values node r := by
  induction round with
  | zero => rfl
  | succ round ih =>
      rw [execute, step_conserves, ih]

/-- By the time a node sends a coordinate upstream, all incoming messages for
that same coordinate have already arrived. Other coordinates may still flow. -/
theorem received_zero_after (round : ℕ) (state : State n k S) (p : Packet n k)
    (hp : time p ≤ round) : received round state (source p) p.1 = 0 := by
  cases hr : Model.receive (plan n k) round (source p) (packetState state) with
  | none => simp [received, hr]
  | some message =>
      obtain ⟨q, value⟩ := message
      obtain ⟨ht, hd, _⟩ := Model.receive_spec (plan n k) round (source p)
        (packetState state) q value hr
      change time q = round at ht
      have hkey : q.1 ≠ p.1 := by
        intro heq
        have hpos : 0 < (parent q.2).val := by
          change parent q.2 = p.2.val at hd
          rw [hd]
          exact p.2.property
        have hchild : (⟨parent q.2, hpos⟩ : Child n) = p.2 := Subtype.ext hd
        have hbefore := child_before q hpos
        rw [heq, hchild] at hbefore
        change time q < time p at hbefore
        omega
      simp [received, hr, hkey]

theorem step_zero_after (round : ℕ) (state : State n k S) (p : Packet n k)
    (hp : time p ≤ round)
    (hstate : time p < round → state (source p) p.1 = 0) :
    step round state (source p) p.1 = 0 := by
  rw [step, received_zero_after round state p hp, add_zero]
  by_cases hnow : time p = round
  · have hex : ∃ q : Packet n k, time q = round ∧ source q = source p ∧ q.1 = p.1 :=
      ⟨p, hnow, rfl, rfl⟩
    simp [retained, hex]
  · have hzero := hstate (by omega)
    unfold retained
    split_ifs <;> simp [hzero]

/-- Every nonroot accumulator is zero after its single upstream transmission. -/
theorem execute_zero_after (values : Fin n → Fin k → S) (p : Packet n k)
    (round : ℕ) (hp : time p < round) : execute values round (source p) p.1 = 0 := by
  induction round with
  | zero => omega
  | succ round ih =>
      exact step_zero_after round _ p (by omega) ih

/-- Coordinatewise aggregation of `k` initially private values per processor
finishes in exactly the public `2*k+2*ceil(log₂ n)` round budget. -/
theorem aggregates (hn : 0 < n) (values : Fin n → Fin k → S) (r : Fin k) :
    execute values (rounds n k) (root hn) r = ∑ node, values node r := by
  have htotal := execute_conserves values (rounds n k) r
  have hroot : (∑ node, execute values (rounds n k) node r) =
      execute values (rounds n k) (root hn) r := by
    apply Finset.sum_eq_single (root hn)
    · intro node _ hne
      have hpos : 0 < node.val := by
        by_contra hnonpos
        apply hne
        apply Fin.ext
        change node.val = 0
        omega
      exact execute_zero_after values (r, ⟨node, hpos⟩) (rounds n k) (time_lt_rounds _)
    · simp
  rw [hroot] at htotal
  exact htotal

omit [AddCommMonoid S] in
/-- The actual additive relay execution has strict capacity in every round. -/
theorem port_capacity (state : State n k S) (round : ℕ) (node : Fin n) :
    ((Model.transmitted (plan n k) round (packetState state)).filter
      (fun p => source p = node)).card ≤ 1 ∧
    ((Model.transmitted (plan n k) round (packetState state)).filter
      (fun p => destination p = node)).card ≤ 1 :=
  ⟨Model.actual_send_capacity _ _ _ _, Model.actual_receive_capacity _ _ _ _⟩

end
end Execution

end SparseMM.PipelinedAggregation

namespace SparseMM.ScalarSystem

variable {Packet NodeState Value : Type*} {n rounds : ℕ}
variable [Fintype Packet] [DecidableEq Packet]
variable {source destination : Packet → Fin n}

noncomputable section

/-- Public packet labels are not transmitted; each physical message contains
only its value and the destination selected by the sender's public code. -/
def send (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (round : ℕ) (node : Fin n) (state : NodeState) : Option (Fin n × Value) :=
  (Model.send plan round node (project node state)).map fun message =>
    (destination message.1, message.2)

def restore (plan : Model.StaticPlan source destination rounds)
    (round : ℕ) (node : Fin n) (inbox : Fin n → Option Value) : Option (Packet × Value) :=
  (Model.incomingLabel plan round node).bind fun p =>
    (inbox (source p)).map fun value => (p, value)

/-- A conventional local message-passing system with one scalar payload.
Its readout is supplied separately by the toolbox interfaces below. -/
def system (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (update : ℕ → Fin n → NodeState → Option (Packet × Value) → NodeState) :
    BroadcastLower.System n NodeState Value where
  send := send plan project
  update := fun round node state inbox => update round node state (restore plan round node inbox)
  output := fun _ _ => false

omit [DecidableEq Packet] in
theorem send_spec (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (round : ℕ) (node : Fin n) (state : NodeState) (receiver : Fin n) (value : Value)
    (h : send plan project round node state = some (receiver, value)) :
    ∃ p, Model.send plan round node (project node state) = some (p, value) ∧
      destination p = receiver := by
  unfold send at h
  cases hm : Model.send plan round node (project node state) with
  | none => simp [hm] at h
  | some message =>
      obtain ⟨p, v⟩ := message
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hreceiver, rfl⟩ := h
      exact ⟨p, rfl, hreceiver⟩

omit [DecidableEq Packet] in
theorem restores_model (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (update : ℕ → Fin n → NodeState → Option (Packet × Value) → NodeState)
    (round : ℕ) (state : Fin n → NodeState) (node : Fin n) :
    restore plan round node ((system plan project update).inbox round state node) =
      Model.receive plan round node (fun sender => project sender (state sender)) := by
  unfold restore Model.receive
  cases hi : Model.incomingLabel plan round node with
  | none => simp
  | some p =>
      simp only [Option.bind_some]
      dsimp only [BroadcastLower.System.inbox, system]
      unfold send
      cases hs : Model.send plan round (source p) (project (source p) (state (source p))) with
      | none => simp
      | some message =>
          obtain ⟨q, value⟩ := message
          have hq := Model.outgoingLabel_spec plan round (source p) q
            (Model.send_spec plan round (source p) _ q value hs).1
          have hp := Model.incomingLabel_spec plan round node p hi
          have heq : q = p := plan.legal q (Finset.mem_univ _) p (Finset.mem_univ _)
            (Fin.ext (hq.1.trans hp.1.symm)) (Or.inl hq.2.1)
          subst q
          simp [hp.2.1]

omit [DecidableEq Packet] in
theorem step_eq (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (update : ℕ → Fin n → NodeState → Option (Packet × Value) → NodeState)
    (round : ℕ) (state : Fin n → NodeState) :
    (system plan project update).step round state = fun node =>
      update round node (state node)
        (Model.receive plan round node (fun sender => project sender (state sender))) := by
  funext node
  change update round node (state node) (restore plan round node
    ((system plan project update).inbox round state node)) = _
  rw [restores_model]

omit [DecidableEq Packet] in
/-- The scalar system has one actual send and at most one actual receive at
every node on every state, even beyond the stated finite execution budget. -/
theorem legalAt (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (update : ℕ → Fin n → NodeState → Option (Packet × Value) → NodeState)
    (round : ℕ) (state : Fin n → NodeState) :
    (system plan project update).LegalAt round state := by
  intro receiver
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have extract (sender : Fin n)
      (hs : ((system plan project update).inbox round state receiver sender).isSome) :
      ∃ p value, Model.send plan round sender (project sender (state sender)) = some (p, value) ∧
        destination p = receiver := by
    unfold BroadcastLower.System.inbox at hs
    dsimp only [system] at hs
    cases hm : send plan project round sender (state sender) with
    | none => simp [hm] at hs
    | some message =>
        obtain ⟨dest, value⟩ := message
        have hd : dest = receiver := by simpa [hm] using hs
        obtain ⟨p, hp, hdest⟩ := send_spec plan project round sender (state sender) dest value hm
        exact ⟨p, value, hp, hdest.trans hd⟩
  obtain ⟨p, value, hp, hpd⟩ := extract a (Finset.mem_filter.mp ha).2
  obtain ⟨q, value', hq, hqd⟩ := extract b (Finset.mem_filter.mp hb).2
  have hps := Model.outgoingLabel_spec plan round a p
    (Model.send_spec plan round a _ p value hp).1
  have hqs := Model.outgoingLabel_spec plan round b q
    (Model.send_spec plan round b _ q value' hq).1
  have heq : p = q := plan.legal p (Finset.mem_univ _) q (Finset.mem_univ _)
    (Fin.ext (hps.1.trans hqs.1.symm)) (Or.inr (hpd.trans hqd.symm))
  exact hps.2.1.symm.trans ((congrArg source heq).trans hqs.2.1)

omit [DecidableEq Packet] in
theorem no_self (plan : Model.StaticPlan source destination rounds)
    (project : Fin n → NodeState → Model.LocalState Packet Value)
    (update : ℕ → Fin n → NodeState → Option (Packet × Value) → NodeState)
    (round : ℕ) (node : Fin n) (state : NodeState) (receiver : Fin n) (value : Value)
    (h : (system plan project update).send round node state = some (receiver, value)) :
    node ≠ receiver := by
  dsimp only [system] at h
  obtain ⟨p, hp, hd⟩ := send_spec plan project round node state receiver value h
  have hne := (Model.outgoingLabel_spec plan round node p
    (Model.send_spec plan round node _ p value hp).1).2.2
  intro heq
  exact hne (hd.trans heq.symm)

end
end SparseMM.ScalarSystem

namespace SparseMM.PipelinedBroadcast

universe u

noncomputable section

def system (n k : ℕ) (Value : Type u) :
    BroadcastLower.System n (Fin k → Option Value) Value :=
  ScalarSystem.system (plan n k) (fun _ memory p => memory p.1)
    (fun _ _ memory message => accept memory message)

theorem system_step {n k : ℕ} {Value : Type u} (round : ℕ) (state : State n k Value) :
    (system n k Value).step round state = step round state := by
  exact ScalarSystem.step_eq _ _ _ _ _

theorem system_execute {n k : ℕ} {Value : Type u} (hn : 0 < n)
    (values : Fin k → Value) (round : ℕ) :
    (system n k Value).execute (initial hn values) round = execute hn values round := by
  induction round with
  | zero => rfl
  | succ round ih =>
      rw [BroadcastLower.System.execute, ih, system_step]
      rfl

/-- Compact operational broadcast interface. A single public scalar-message
system and local initialization/readout work for every private source vector. -/
theorem exists_broadcast {n : ℕ} (hn : 0 < n) (k : ℕ) (Value : Type u) :
    ∃ NodeState : Type u, ∃ code : BroadcastLower.System n NodeState Value,
      ∃ init : Fin n → (Fin k → Option Value) → NodeState,
      ∃ readout : Fin n → NodeState → Fin k → Option Value,
        (∀ round sender memory receiver value,
          code.send round sender memory = some (receiver, value) → sender ≠ receiver) ∧
        ∀ values : Fin k → Value,
          (∀ round, code.LegalAt round
            (code.execute (fun node => init node
              (fun r => if node.val = 0 then some (values r) else none)) round)) ∧
          ∀ node r, readout node
            (code.execute (fun node => init node
              (fun r => if node.val = 0 then some (values r) else none))
                (2 * k + 2 * Nat.clog 2 n) node) r = some (values r) := by
  refine ⟨Fin k → Option Value, system n k Value, fun _ memory => memory,
    fun _ memory => memory, ?_⟩
  constructor
  · exact ScalarSystem.no_self _ _ _
  · intro values
    have hinitial : (fun node : Fin n => fun r : Fin k =>
      if node.val = 0 then some (values r) else none) = initial hn values := by
      funext node r
      have heq : node.val = 0 ↔ node = root hn := by
        constructor
        · intro h; apply Fin.ext; exact h
        · intro h; exact congrArg Fin.val h
      simp only [initial, heq]
    constructor
    · intro round
      exact ScalarSystem.legalAt _ _ _ _ _
    · intro node r
      rw [hinitial, system_execute]
      exact broadcasts hn values node r

end
end SparseMM.PipelinedBroadcast

namespace SparseMM.PipelinedAggregation

universe u

noncomputable section

def system (n k : ℕ) (S : Type u) [AddCommMonoid S] :
    BroadcastLower.System n (Fin k → S) S :=
  ScalarSystem.system (plan n k) (fun _ memory p => some (memory p.1))
    (fun round node memory message =>
      fun r => retained round (fun _ => memory) node r +
        match message with
        | none => 0
        | some (p, value) => if p.1 = r then value else 0)

theorem system_step {n k : ℕ} {S : Type u} [AddCommMonoid S]
    (round : ℕ) (state : State n k S) :
    (system n k S).step round state = step round state := by
  exact ScalarSystem.step_eq _ _ _ _ _

theorem system_execute {n k : ℕ} {S : Type u} [AddCommMonoid S]
    (values : Fin n → Fin k → S) (round : ℕ) :
    (system n k S).execute values round = execute values round := by
  induction round with
  | zero => rfl
  | succ round ih =>
      rw [BroadcastLower.System.execute, ih, system_step]
      rfl

/-- Compact operational aggregation interface. Each initialization uses only
that processor's private inputs; the root obtains every coordinate sum. -/
theorem exists_aggregation {n : ℕ} (hn : 0 < n) (k : ℕ) (S : Type u) [AddCommMonoid S] :
    ∃ NodeState : Type u, ∃ code : BroadcastLower.System n NodeState S,
      ∃ init : Fin n → (Fin k → S) → NodeState,
      ∃ readout : Fin n → NodeState → Fin k → S,
        (∀ round sender memory receiver value,
          code.send round sender memory = some (receiver, value) → sender ≠ receiver) ∧
        ∀ values : Fin n → Fin k → S,
          (∀ round, code.LegalAt round
            (code.execute (fun node => init node (values node)) round)) ∧
          ∀ r, readout (⟨0, hn⟩ : Fin n)
            (code.execute (fun node => init node (values node))
              (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r = ∑ node, values node r := by
  refine ⟨Fin k → S, system n k S, fun _ memory => memory, fun _ memory => memory, ?_⟩
  constructor
  · exact ScalarSystem.no_self _ _ _
  · intro values
    constructor
    · intro round
      exact ScalarSystem.legalAt _ _ _ _ _
    · intro r
      rw [system_execute]
      exact aggregates hn values r

end
end SparseMM.PipelinedAggregation
