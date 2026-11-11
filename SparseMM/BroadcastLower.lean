module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM.BroadcastLower

open scoped BigOperators

/-- A deterministic local message-passing system. An outgoing message can
depend on time, the sender's public identifier, and its entire local state.
The inbox exposes sender identity and silence, so these communication channels
are not excluded from the lower bound. -/
structure System (n : ℕ) (State Message : Type*) where
  send : ℕ → Fin n → State → Option (Fin n × Message)
  update : ℕ → Fin n → State → (Fin n → Option Message) → State
  output : Fin n → State → Bool

variable {n : ℕ} {State Message : Type*}

namespace System

variable (system : System n State Message)

/-- Each actual outgoing message is delivered to its specified destination.
An inbox is indexed by sender, including the absence of a message. -/
def inbox (time : ℕ) (state : Fin n → State) (receiver sender : Fin n) : Option Message :=
  match system.send time sender (state sender) with
  | none => none
  | some (destination, value) => if destination = receiver then some value else none

/-- The usual one-receive constraint. The influence bound below holds even
without this restriction, and therefore also for every legal execution. -/
def LegalAt (time : ℕ) (state : Fin n → State) : Prop :=
  ∀ receiver, (Finset.univ.filter fun sender =>
    (system.inbox time state receiver sender).isSome).card ≤ 1

def step (time : ℕ) (state : Fin n → State) : Fin n → State :=
  fun node => system.update time node (state node) (system.inbox time state node)

def execute (initial : Fin n → State) : ℕ → Fin n → State
  | 0 => initial
  | time + 1 => system.step time (execute initial time)

end System

noncomputable def changed (left right : Fin n → State) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun node => left node ≠ right node

namespace System

variable (system : System n State Message)

/-- Destinations reached by a specified set of senders in one execution. -/
def destinations (time : ℕ) (state : Fin n → State) (senders : Finset (Fin n)) :
    Finset (Fin n) :=
  senders.biUnion fun sender =>
    match system.send time sender (state sender) with
    | none => ∅
    | some (destination, _) => {destination}

theorem destinations_card_le (time : ℕ) (state : Fin n → State) (senders : Finset (Fin n)) :
    (system.destinations time state senders).card ≤ senders.card := by
  unfold destinations
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _sender ∈ senders, 1 := by
      apply Finset.sum_le_sum
      intro sender _
      cases system.send time sender (state sender) <;> simp
    _ = _ := by simp

theorem inbox_none_of_not_destination (time : ℕ) (state : Fin n → State)
    (senders : Finset (Fin n)) (receiver sender : Fin n)
    (hsender : sender ∈ senders) (hreceiver : receiver ∉ system.destinations time state senders) :
    system.inbox time state receiver sender = none := by
  unfold inbox
  cases hs : system.send time sender (state sender) with
  | none => rfl
  | some message =>
      obtain ⟨destination, value⟩ := message
      have hne : destination ≠ receiver := by
        intro hsame
        apply hreceiver
        apply Finset.mem_biUnion.mpr
        exact ⟨sender, hsender, by simp [hs, hsame]⟩
      simp [hne]

/-- A newly differing state is either an already differing local state or a
recipient of a message from a differing sender in at least one of the two
executions. Counting both destination sets handles data-dependent addressing. -/
theorem changed_step_subset (time : ℕ) (left right : Fin n → State) :
    changed (system.step time left) (system.step time right) ⊆
      changed left right ∪ system.destinations time left (changed left right) ∪
        system.destinations time right (changed left right) := by
  classical
  intro node hnode
  by_contra hnot
  have hnot' : node ∉ changed left right ∧
      node ∉ system.destinations time left (changed left right) ∧
      node ∉ system.destinations time right (changed left right) := by
    simpa only [Finset.mem_union, not_or, and_assoc] using hnot
  have heq : left node = right node := by simpa [changed] using hnot'.1
  have hinbox : system.inbox time left node = system.inbox time right node := by
    funext sender
    by_cases hsender : sender ∈ changed left right
    · rw [system.inbox_none_of_not_destination time left _ node sender hsender hnot'.2.1,
        system.inbox_none_of_not_destination time right _ node sender hsender hnot'.2.2]
    · have hs : left sender = right sender := by simpa [changed] using hsender
      simp only [inbox, hs]
  have hstep : system.step time left node = system.step time right node := by
    simp only [step, heq, hinbox]
  exact (Finset.mem_filter.mp hnode).2 hstep

theorem changed_step_card_le (time : ℕ) (left right : Fin n → State) :
    (changed (system.step time left) (system.step time right)).card ≤
      3 * (changed left right).card := by
  have hsub := Finset.card_le_card (system.changed_step_subset time left right)
  have hleft := system.destinations_card_le time left (changed left right)
  have hright := system.destinations_card_le time right (changed left right)
  have hfirst := Finset.card_union_le (changed left right)
    (system.destinations time left (changed left right))
  have hsecond := Finset.card_union_le
    (changed left right ∪ system.destinations time left (changed left right))
    (system.destinations time right (changed left right))
  omega

/-- The number of nodes whose states distinguish two initial configurations
grows by at most a factor of three per communication round. -/
theorem changed_execute_card_le (left right : Fin n → State) (time : ℕ) :
    (changed (system.execute left time) (system.execute right time)).card ≤
      3 ^ time * (changed left right).card := by
  induction time with
  | zero => simp [execute]
  | succ time ih =>
      have hstep := system.changed_step_card_le time
        (system.execute left time) (system.execute right time)
      calc
        _ ≤ 3 * (changed (system.execute left time) (system.execute right time)).card := hstep
        _ ≤ 3 * (3 ^ time * (changed left right).card) := Nat.mul_le_mul_left 3 ih
        _ = _ := by simp only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- A correct broadcast of one initially private bit requires `n <= 3^T`.
This is a lower bound for arbitrary deterministic local addressing and
unbounded message alphabets. It counts information carried by silence and
sender identities, and does not assume an input-oblivious schedule. -/
theorem broadcast_requires_rounds (source : Fin n) (left right : Fin n → State)
    (hlocal : ∀ node, node ≠ source → left node = right node) (time : ℕ)
    (hfalse : ∀ node, system.output node (system.execute left time node) = false)
    (htrue : ∀ node, system.output node (system.execute right time node) = true) :
    n ≤ 3 ^ time := by
  classical
  have hstart : (changed left right).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : a = source := by
      by_contra h
      exact (Finset.mem_filter.mp ha).2 (hlocal a h)
    have hb' : b = source := by
      by_contra h
      exact (Finset.mem_filter.mp hb).2 (hlocal b h)
    exact ha'.trans hb'.symm
  have hfinal : changed (system.execute left time) (system.execute right time) = Finset.univ := by
    ext node
    simp only [changed, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro heq
    have hout := congrArg (system.output node) heq
    rw [hfalse node, htrue node] at hout
    contradiction
  have hbound := system.changed_execute_card_le left right time
  rw [hfinal, Finset.card_univ, Fintype.card_fin] at hbound
  exact hbound.trans (by simpa using Nat.mul_le_mul_left (3 ^ time) hstart)

end System

end SparseMM.BroadcastLower
