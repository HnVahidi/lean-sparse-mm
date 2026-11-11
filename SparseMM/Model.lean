module

public import SparseMM.Routing

/-!
# Local execution of public static redistributions

A local memory stores optional values under packet labels. Initially a node
has a packet value only when it is that packet's source. A sender reads only
its own local memory. The network delivers the sender's actual message, and
the receiver updates its own memory using only that message. No local step
reads another node's memory directly. Self-destined packets remain local.

The scheduling code is chosen before the numerical packet values. Its legal
slots guarantee one send and one receive at each node in every round.
-/

@[expose] public section

namespace SparseMM.Model

variable {Packet Node Value : Type*}

/-- Public code for one finite redistribution phase. -/
structure StaticPlan [Fintype Packet] (source destination : Packet → Node) (rounds : ℕ) where
  slot : Packet → Fin rounds
  legal : Routing.LegalOn Finset.univ source destination slot

/-- One node's memory. Missing packet labels carry no numerical information. -/
abbrev LocalState (Packet Value : Type*) := Packet → Option Value

/-- A configuration consists of a separate local memory at each node. -/
abbrev Configuration (Packet Node Value : Type*) := Node → LocalState Packet Value

section Execution

variable [Fintype Packet] [DecidableEq Packet] [DecidableEq Node]
variable {source destination : Packet → Node} {rounds : ℕ}

noncomputable section

/-- Initially each node receives exactly its own source packet values. -/
def initial (source : Packet → Node) (values : Packet → Value) :
    Configuration Packet Node Value :=
  fun node p => if source p = node then some (values p) else none

/-- The next outgoing label is computed solely from public code. -/
def outgoingLabel (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node) :
    Option Packet :=
  if h : ∃ p, (plan.slot p).val = time ∧ source p = node ∧ destination p ≠ node then
    some (Classical.choose h)
  else none

/-- The incoming channel is also selected solely from public code. -/
def incomingLabel (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node) :
    Option Packet :=
  if h : ∃ p, (plan.slot p).val = time ∧ destination p = node ∧ source p ≠ node then
    some (Classical.choose h)
  else none

/-- A sender reads the selected packet from its own memory. -/
def send (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (memory : LocalState Packet Value) : Option (Packet × Value) :=
  (outgoingLabel plan time node).bind fun p => (memory p).map fun value => (p, value)

/-- The network receives an actual outgoing message on the selected public
channel. This is the only inter-node connection in the operational semantics. -/
def receive (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state : Configuration Packet Node Value) : Option (Packet × Value) :=
  (incomingLabel plan time node).bind fun p => send plan time (source p) (state (source p))

/-- A local update uses only old local memory and its received message. -/
def accept (memory : LocalState Packet Value) (message : Option (Packet × Value)) :
    LocalState Packet Value :=
  fun p => match message with
    | none => memory p
    | some (q, value) => if p = q then some value else memory p

/-- One synchronous round: local sends are followed by local receives. -/
def step (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) : Configuration Packet Node Value :=
  fun node => accept (state node) (receive plan time node state)

/-- Execute a finite number of rounds from a supplied configuration. -/
def executeFrom (plan : StaticPlan source destination rounds) :
    ℕ → Configuration Packet Node Value → Configuration Packet Node Value
  | 0, state => state
  | time + 1, state => step plan time (executeFrom plan time state)

/-- Execute the public phase from source-local numerical inputs. -/
def execute (plan : StaticPlan source destination rounds) (values : Packet → Value)
    (time : ℕ) : Configuration Packet Node Value :=
  executeFrom plan time (initial source values)

omit [Fintype Packet] [DecidableEq Packet] in
/-- Changing remote numerical inputs cannot change a node's initial memory. -/
theorem initial_locality (values values' : Packet → Value) (node : Node)
    (h : ∀ p, source p = node → values p = values' p) :
    initial source values node = initial source values' node := by
  funext p
  by_cases hp : source p = node
  · simp [initial, hp, h p hp]
  · simp [initial, hp]

omit [DecidableEq Packet] in
/-- Equal local memories produce equal outgoing messages, regardless of all
other nodes' memories. -/
theorem send_locality (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state state' : Configuration Packet Node Value) (h : state node = state' node) :
    send plan time node (state node) = send plan time node (state' node) := by
  rw [h]

omit [Fintype Packet] in
/-- A receiver's next memory depends only on its own old memory and the one
message supplied to it. -/
theorem accept_locality (memory memory' : LocalState Packet Value)
    (message message' : Option (Packet × Value))
    (hlocal : memory = memory') (hmessage : message = message') :
    accept memory message = accept memory' message' := by
  rw [hlocal, hmessage]

omit [DecidableEq Packet] in
theorem outgoingLabel_spec (plan : StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (p : Packet)
    (h : outgoingLabel plan time node = some p) :
    (plan.slot p).val = time ∧ source p = node ∧ destination p ≠ node := by
  unfold outgoingLabel at h
  split at h
  next hex =>
    have hp : Classical.choose hex = p := Option.some.inj h
    rw [← hp]
    exact Classical.choose_spec hex
  next => contradiction

omit [DecidableEq Packet] in
theorem incomingLabel_spec (plan : StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (p : Packet)
    (h : incomingLabel plan time node = some p) :
    (plan.slot p).val = time ∧ destination p = node ∧ source p ≠ node := by
  unfold incomingLabel at h
  split at h
  next hex =>
    have hp : Classical.choose hex = p := Option.some.inj h
    rw [← hp]
    exact Classical.choose_spec hex
  next => contradiction

omit [DecidableEq Packet] in
theorem outgoingLabel_eq_some (plan : StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (p : Packet)
    (ht : (plan.slot p).val = time) (hs : source p = node) (hd : destination p ≠ node) :
    outgoingLabel plan time node = some p := by
  have hex : ∃ q, (plan.slot q).val = time ∧ source q = node ∧ destination q ≠ node :=
    ⟨p, ht, hs, hd⟩
  unfold outgoingLabel
  rw [dite_eq_left hex]
  congr 1
  obtain ⟨hqt, hqs, _⟩ := Classical.choose_spec hex
  exact plan.legal _ (Finset.mem_univ _) p (Finset.mem_univ _)
    (Fin.ext (hqt.trans ht.symm)) (Or.inl (hqs.trans hs.symm))

omit [DecidableEq Packet] in
theorem incomingLabel_eq_some (plan : StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (p : Packet)
    (ht : (plan.slot p).val = time) (hd : destination p = node) (hs : source p ≠ node) :
    incomingLabel plan time node = some p := by
  have hex : ∃ q, (plan.slot q).val = time ∧ destination q = node ∧ source q ≠ node :=
    ⟨p, ht, hd, hs⟩
  unfold incomingLabel
  rw [dite_eq_left hex]
  congr 1
  obtain ⟨hqt, hqd, _⟩ := Classical.choose_spec hex
  exact plan.legal _ (Finset.mem_univ _) p (Finset.mem_univ _)
    (Fin.ext (hqt.trans ht.symm)) (Or.inr (hqd.trans hd.symm))

omit [DecidableEq Packet] in
/-- Any actual sent message uses its publicly scheduled label and reads the
numerical value from the sender's local memory. -/
theorem send_spec (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (memory : LocalState Packet Value) (p : Packet) (value : Value)
    (h : send plan time node memory = some (p, value)) :
    outgoingLabel plan time node = some p ∧ memory p = some value := by
  unfold send at h
  cases ho : outgoingLabel plan time node with
  | none => simp [ho] at h
  | some q =>
    cases hv : memory q with
    | none => simp [ho, hv] at h
    | some v =>
      simp only [ho, Option.bind_some, hv, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hv⟩

omit [DecidableEq Packet] in
/-- Every received message is an actual message sent by its source, on its
assigned slot, to this destination. -/
theorem receive_spec (plan : StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state : Configuration Packet Node Value) (p : Packet) (value : Value)
    (h : receive plan time node state = some (p, value)) :
    (plan.slot p).val = time ∧ destination p = node ∧ source p ≠ node ∧
      send plan time (source p) (state (source p)) = some (p, value) := by
  unfold receive at h
  cases hi : incomingLabel plan time node with
  | none => simp [hi] at h
  | some q =>
    simp only [hi, Option.bind_some] at h
    obtain ⟨hot, hos, _⟩ := outgoingLabel_spec plan time (source q) p
      (send_spec plan time (source q) (state (source q)) p value h).1
    obtain ⟨hqt, hqd, hqs⟩ := incomingLabel_spec plan time node q hi
    have hpq : p = q := plan.legal p (Finset.mem_univ _) q (Finset.mem_univ _)
      (Fin.ext (hot.trans hqt.symm)) (Or.inl hos)
    subst p
    exact ⟨hqt, hqd, hqs, h⟩

omit [DecidableEq Packet] in
/-- The network delivers every actual sent message to its destination in the
same round. In particular, selecting an incoming channel drops no message. -/
theorem sent_is_received (plan : StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (state : Configuration Packet Node Value)
    (p : Packet) (value : Value)
    (h : send plan time node (state node) = some (p, value)) :
    receive plan time (destination p) state = some (p, value) := by
  obtain ⟨ho, _⟩ := send_spec plan time node (state node) p value h
  obtain ⟨ht, hs, hd⟩ := outgoingLabel_spec plan time node p ho
  have hsne : source p ≠ destination p := by
    intro heq
    exact hd (heq.symm.trans hs)
  unfold receive
  rw [incomingLabel_eq_some plan time (destination p) p ht rfl hsne]
  simp only [Option.bind_some, hs]
  exact h

/-- Exact single-packet behavior of a round. A transfer copies the source's
existing local value; all other local memory entries remain unchanged. -/
theorem step_apply (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) (node : Node) (p : Packet) :
    step plan time state node p =
      if (plan.slot p).val = time ∧ destination p = node ∧ source p ≠ node then
        match state (source p) p with
        | some value => some value
        | none => state node p
      else state node p := by
  by_cases hp : (plan.slot p).val = time ∧ destination p = node ∧ source p ≠ node
  · obtain ⟨ht, hd, hs⟩ := hp
    rw [ite_eq_left ⟨ht, hd, hs⟩]
    have ho : outgoingLabel plan time (source p) = some p := by
      apply outgoingLabel_eq_some plan time (source p) p ht rfl
      intro heq
      exact hs (heq.symm.trans hd)
    simp only [step, receive,
      incomingLabel_eq_some plan time node p ht hd hs, Option.bind_some,
      send, ho]
    cases hv : state (source p) p with
    | none =>
      simp [accept]
    | some value =>
      simp [accept]
  · cases hr : receive plan time node state with
    | none => simp [step, hr, accept, hp]
    | some message =>
      obtain ⟨q, value⟩ := message
      have hq := receive_spec plan time node state q value hr
      have hne : p ≠ q := by
        intro heq
        subst q
        exact hp ⟨hq.1, hq.2.1, hq.2.2.1⟩
      simp [step, hr, accept, hp, hne]

/-- A node's own source value is retained throughout a phase, including when
the packet is also destined to that same node. -/
theorem executeFrom_source (plan : StaticPlan source destination rounds)
    (state : Configuration Packet Node Value) (p : Packet) (time : ℕ) :
    executeFrom plan time state (source p) p = state (source p) p := by
  induction time with
  | zero => rfl
  | succ time ih =>
      simpa only [executeFrom, step_apply, ne_eq, not_true_eq_false, and_false,
        ite_false] using ih

/-- If a packet is present at its source, it is present at its destination
after its assigned slot. Initial memory at all other nodes is unrestricted. -/
theorem executeFrom_delivery (plan : StaticPlan source destination rounds)
    (state : Configuration Packet Node Value) (p : Packet) (value : Value)
    (hvalue : state (source p) p = some value) :
    ∀ time, (plan.slot p).val < time →
      executeFrom plan time state (destination p) p = some value := by
  intro time
  by_cases hself : source p = destination p
  · intro _
    rw [← hself, executeFrom_source]
    exact hvalue
  · induction time with
    | zero => intro ht; omega
    | succ time ih =>
        intro ht
        rw [executeFrom, step_apply]
        by_cases hnow : (plan.slot p).val = time
        · rw [ite_eq_left ⟨hnow, rfl, hself⟩, executeFrom_source, hvalue]
        · rw [ite_eq_right (by intro h; exact hnow h.1)]
          exact ih (by omega)

/-- A public redistribution works from any configuration supplying each
packet at its own source. This is the phase-composition interface. -/
theorem executeFrom_delivers (plan : StaticPlan source destination rounds)
    (state : Configuration Packet Node Value) (values : Packet → Value)
    (hvalue : ∀ p, state (source p) p = some (values p)) (p : Packet) :
    executeFrom plan rounds state (destination p) p = some (values p) := by
  exact executeFrom_delivery plan state p (values p) (hvalue p) rounds (plan.slot p).isLt

/-- The source-local initialization suffices for exact delivery of every
packet. Numerical inputs are never supplied at remote nodes initially. -/
theorem execute_delivers (plan : StaticPlan source destination rounds)
    (values : Packet → Value) (p : Packet) :
    execute plan values rounds (destination p) p = some (values p) := by
  apply executeFrom_delivers
  intro q
  simp [initial]

/-- Packet labels of actual outgoing numerical messages in one round. -/
def transmitted (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) : Finset Packet := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ value, send plan time (source p) (state (source p)) = some (p, value)

omit [DecidableEq Packet] in
/-- Every actual execution, including configurations missing some packets,
has at most one transmitted packet per sender in a round. -/
theorem actual_send_capacity (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) (node : Node) :
    ((transmitted plan time state).filter (fun p => source p = node)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hps⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqs⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, value, hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, value', hv'⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpt, _, _⟩ := outgoingLabel_spec plan time (source p) p
    (send_spec plan time (source p) (state (source p)) p value hv).1
  obtain ⟨hqt, _, _⟩ := outgoingLabel_spec plan time (source q) q
    (send_spec plan time (source q) (state (source q)) q value' hv').1
  exact plan.legal p (Finset.mem_univ _) q (Finset.mem_univ _)
    (Fin.ext (hpt.trans hqt.symm)) (Or.inl (hps.trans hqs.symm))

omit [DecidableEq Packet] in
/-- Every actual execution has at most one transmitted packet per receiver
in a round. No collision rejection or global stopping rule is used. -/
theorem actual_receive_capacity (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) (node : Node) :
    ((transmitted plan time state).filter (fun p => destination p = node)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hqd⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, value, hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, value', hv'⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpt, _, _⟩ := outgoingLabel_spec plan time (source p) p
    (send_spec plan time (source p) (state (source p)) p value hv).1
  obtain ⟨hqt, _, _⟩ := outgoingLabel_spec plan time (source q) q
    (send_spec plan time (source q) (state (source q)) q value' hv').1
  exact plan.legal p (Finset.mem_univ _) q (Finset.mem_univ _)
    (Fin.ext (hpt.trans hqt.symm)) (Or.inr (hpd.trans hqd.symm))

omit [DecidableEq Packet] in
/-- An actual message always crosses to a distinct machine; self-destined
packets require no communication. -/
theorem transmitted_not_self (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) (p : Packet)
    (hp : p ∈ transmitted plan time state) : source p ≠ destination p := by
  classical
  obtain ⟨_, value, hv⟩ := Finset.mem_filter.mp hp
  have hne := (outgoingLabel_spec plan time (source p) p
    (send_spec plan time (source p) (state (source p)) p value hv).1).2.2
  exact Ne.symm hne

/-- One static code is chosen from public ownership maps before all numerical
values. Its local execution delivers every value in at most twice the load
bound many strict low-bandwidth rounds. -/
theorem exists_public_redistribution (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card ≤ D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card ≤ D) :
    ∃ plan : StaticPlan source destination (2 * D),
      ∀ (values : Packet → Value) (p : Packet),
        execute plan values (2 * D) (destination p) p = some (values p) := by
  obtain ⟨slot, hlegal⟩ := Routing.exists_schedule source destination D hout hin
  refine ⟨⟨slot, hlegal⟩, ?_⟩
  intro values p
  exact execute_delivers _ values p

end

end Execution

end SparseMM.Model
