module

public import SparseMM.BroadcastLower
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace SparseMM.AggregationLower

open scoped BigOperators

variable {n : ℕ} {State Message : Type*}

def singleInbox (sender : Fin n) (message : Message) : Fin n → Option Message :=
  fun node => if node = sender then some message else none

/-- A sender's possible received message depends only on that sender's state.
The destination and payload may both depend on that state. -/
def messageAt (system : BroadcastLower.System n State Message) (time : ℕ)
    (receiver sender : Fin n) (remote : State) : Option Message :=
  match system.send time sender remote with
  | none => none
  | some (destination, message) => if destination = receiver then some message else none

def baseValue (system : BroadcastLower.System n State Message) (time : ℕ)
    (receiver : Fin n) (observable : State → ℝ) (localState : State) : ℝ :=
  observable (system.update time receiver localState (fun _ => none))

/-- The correction contributed by one potential incoming sender. -/
def contribution (system : BroadcastLower.System n State Message) (time : ℕ)
    (receiver sender : Fin n) (observable : State → ℝ) (localState remote : State) : ℝ :=
  match messageAt system time receiver sender remote with
  | none => 0
  | some message =>
      observable (system.update time receiver localState (singleInbox sender message)) -
        baseValue system time receiver observable localState

/-- Legality on this actual input makes the receiver's next observable an
affine sum of pairwise local/sender-state observables. Silence is represented
by the base term, so no absence-of-message information is discarded. -/
theorem step_observable_decomposition (system : BroadcastLower.System n State Message)
    (time : ℕ) (state : Fin n → State) (receiver : Fin n) (observable : State → ℝ)
    (hlegal : system.LegalAt time state) :
    observable (system.step time state receiver) =
      baseValue system time receiver observable (state receiver) +
        ∑ sender : Fin n,
          contribution system time receiver sender observable (state receiver) (state sender) := by
  classical
  by_cases hreceived : ∃ sender message, system.inbox time state receiver sender = some message
  · obtain ⟨sender, message, hmessage⟩ := hreceived
    have hother (other : Fin n) (hne : other ≠ sender) :
        system.inbox time state receiver other = none := by
      cases hm : system.inbox time state receiver other with
      | none => rfl
      | some value =>
          have he : other = sender := Finset.card_le_one.mp (hlegal receiver)
            other (by simp [hm]) sender (by simp [hmessage])
          exact (hne he).elim
    have hinbox : system.inbox time state receiver = singleInbox sender message := by
      funext other
      by_cases he : other = sender
      · subst other
        simp [singleInbox, hmessage]
      · simp [singleInbox, he, hother other he]
    have hsum : (∑ other : Fin n,
        contribution system time receiver other observable (state receiver) (state other)) =
          contribution system time receiver sender observable (state receiver) (state sender) := by
      apply Finset.sum_eq_single sender
      · intro other _ hne
        have hm : messageAt system time receiver other (state other) = none := hother other hne
        simp only [contribution, hm]
      · simp
    rw [hsum]
    have hm : messageAt system time receiver sender (state sender) = some message := hmessage
    simp only [BroadcastLower.System.step, hinbox, contribution, hm]
    simp
  · have hnone (sender : Fin n) : system.inbox time state receiver sender = none := by
      cases hm : system.inbox time state receiver sender with
      | none => rfl
      | some value => exact (hreceived ⟨sender, value, hm⟩).elim
    have hinbox : system.inbox time state receiver = fun _ => none := funext hnone
    have hzero : (∑ sender : Fin n,
        contribution system time receiver sender observable (state receiver) (state sender)) = 0 := by
      apply Finset.sum_eq_zero
      intro sender _
      have hm : messageAt system time receiver sender (state sender) = none := hnone sender
      simp only [contribution, hm]
    simp only [BroadcastLower.System.step, hinbox, hzero, add_zero, baseValue]

end SparseMM.AggregationLower
