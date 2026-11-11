module

public import SparseMM.AggregationModel
public import SparseMM.BooleanDegree

@[expose] public section

namespace SparseMM.AggregationLower

open scoped BigOperators
open BooleanDegree

variable {n : ℕ} {State Message : Type*}

/-- Every numerical observable of a local state lies in the indicated Boolean
degree space. State and message alphabets may be arbitrary infinite types. -/
def ObservableDegree {α : Type*} (state : Cube n → α) (k : ℕ) : Prop :=
  ∀ observable : α → ℝ, (fun x => observable (state x)) ∈ Space n k

/-- An arbitrary observable of two local states has degree at most the sum of
their degree bounds. Only the finite set of reachable first states is summed,
so no finite-state or bounded-message-alphabet hypothesis is hidden here. -/
theorem pair_observable_degree {α β : Type*} (left : Cube n → α) (right : Cube n → β)
    (k l : ℕ) (hleft : ObservableDegree left k) (hright : ObservableDegree right l)
    (observable : α → β → ℝ) :
    (fun x => observable (left x) (right x)) ∈ Space n (k + l) := by
  classical
  let reachable := Finset.univ.image left
  have heq : (fun x => observable (left x) (right x)) =
      ∑ q ∈ reachable, (fun x => (if left x = q then (1 : ℝ) else 0) * observable q (right x)) := by
    funext x
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single (left x)]
    · simp
    · intro q _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)).elim
  rw [heq]
  apply BooleanDegree.sum
  intro q _
  exact BooleanDegree.mul (hleft (fun a => if a = q then (1 : ℝ) else 0))
    (hright (observable q))

theorem step_observable_degree (system : BroadcastLower.System n State Message)
    (time : ℕ) (states : Cube n → Fin n → State) (k : ℕ)
    (hstates : ∀ node, ObservableDegree (fun x => states x node) k)
    (hlegal : ∀ x, system.LegalAt time (states x)) (receiver : Fin n) :
    ObservableDegree (fun x => system.step time (states x) receiver) (k + k) := by
  intro observable
  have hbase : (fun x => baseValue system time receiver observable (states x receiver)) ∈
      Space n (k + k) :=
    BooleanDegree.mono (Nat.le_add_right k k)
      (hstates receiver (baseValue system time receiver observable))
  have hterm (sender : Fin n) :
      (fun x => contribution system time receiver sender observable
        (states x receiver) (states x sender)) ∈ Space n (k + k) :=
    pair_observable_degree _ _ k k (hstates receiver) (hstates sender)
      (contribution system time receiver sender observable)
  have heq : (fun x => observable (system.step time (states x) receiver)) =
      (fun x => baseValue system time receiver observable (states x receiver)) +
        ∑ sender : Fin n, (fun x => contribution system time receiver sender observable
          (states x receiver) (states x sender)) := by
    funext x
    simpa only [Pi.add_apply, Finset.sum_apply] using
      step_observable_decomposition system time (states x) receiver observable (hlegal x)
  rw [heq]
  exact BooleanDegree.add hbase (BooleanDegree.sum Finset.univ _ (fun sender _ => hterm sender))

/-- Each processor's initial private state depends only on its own input bit. -/
def initialConfiguration (initial : Fin n → Bool → State) (x : Cube n) : Fin n → State :=
  fun node => initial node (x node)

def stateAt (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (time : ℕ) (node : Fin n) : Cube n → State :=
  fun x => system.execute (initialConfiguration initial x) time node

/-- The degree invariant is proved from actual local execution and validity
on every input through the requested time horizon. -/
theorem observable_stateAt (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time)) :
    ∀ time, time ≤ T → ∀ node, ObservableDegree (stateAt system initial time node) (2 ^ time) := by
  intro time
  induction time with
  | zero =>
      intro _ node observable
      apply BooleanDegree.of_dependsOn (s := {node}) (by simp)
      intro x y hxy
      have hbit := hxy node (Finset.mem_singleton_self node)
      simp only [stateAt, BroadcastLower.System.execute, initialConfiguration, hbit]
  | succ time ih =>
      intro htime node
      have hprevious := ih (show time ≤ T by omega)
      have hnext := step_observable_degree system time
        (fun x => system.execute (initialConfiguration initial x) time) (2 ^ time)
        hprevious (hlegal time (by omega)) node
      change ObservableDegree (fun x => system.step time
        (system.execute (initialConfiguration initial x) time) node) (2 ^ (time + 1))
      simpa only [pow_succ, Nat.mul_two] using hnext

/-- OR of independently distributed bits requires `n <= 2^T`, even with
adaptive recipients, arbitrary message alphabets, sender identities and
communication by silence. Port legality is required on every input. -/
theorem or_requires_rounds (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ) (receiver : Fin n)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time))
    (hcorrect : ∀ x : Cube n, system.output receiver
      (system.execute (initialConfiguration initial x) T receiver) = decide (∃ i, x i = true)) :
    n ≤ 2 ^ T := by
  classical
  have hdegree := observable_stateAt system initial T hlegal T le_rfl receiver
    (fun state => if system.output receiver state then (1 : ℝ) else 0)
  have heq : (fun x => if system.output receiver (stateAt system initial T receiver x)
      then (1 : ℝ) else 0) = orValue (n := n) := by
    funext x
    simp [stateAt, hcorrect, orValue]
  rw [heq] at hdegree
  exact BooleanDegree.or_requires_degree hdegree

/-- The analogous lower bound for AND follows from its full Boolean degree. -/
theorem and_requires_rounds (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ) (receiver : Fin n)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time))
    (hcorrect : ∀ x : Cube n, system.output receiver
      (system.execute (initialConfiguration initial x) T receiver) = decide (∀ i, x i = true)) :
    n ≤ 2 ^ T := by
  classical
  have hdegree := observable_stateAt system initial T hlegal T le_rfl receiver
    (fun state => if system.output receiver state then (1 : ℝ) else 0)
  have heq : (fun x => if system.output receiver (stateAt system initial T receiver x)
      then (1 : ℝ) else 0) = andValue (n := n) := by
    funext x
    simp [stateAt, hcorrect, andValue]
  rw [heq] at hdegree
  exact BooleanDegree.and_requires_degree hdegree

/-- Counting the true bits is at least as hard as OR: a local zero test of the
sum recovers OR, even though the sum itself has algebraic degree one. -/
theorem sum_requires_rounds (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ) (receiver : Fin n)
    (readSum : State → ℕ)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time))
    (hcorrect : ∀ x : Cube n, readSum
      (system.execute (initialConfiguration initial x) T receiver) =
        ∑ i : Fin n, if x i then 1 else 0) :
    n ≤ 2 ^ T := by
  classical
  have hdegree := observable_stateAt system initial T hlegal T le_rfl receiver
    (fun state => if 0 < readSum state then (1 : ℝ) else 0)
  have heq : (fun x => if 0 < readSum (stateAt system initial T receiver x)
      then (1 : ℝ) else 0) = orValue (n := n) := by
    funext x
    simp only [stateAt, hcorrect, orValue]
    congr 1
    apply propext
    constructor
    · intro hpos
      by_contra hnone
      have hzero : (∑ i : Fin n, if x i then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        cases hx : x i
        · simp [hx]
        · exact (hnone ⟨i, hx⟩).elim
      omega
    · rintro ⟨i, hi⟩
      have hterm : 1 ≤ ∑ j : Fin n, if x j then 1 else 0 := by
        simpa [hi] using Finset.single_le_sum
          (fun j _ => Nat.zero_le (if x j then 1 else 0)) (Finset.mem_univ i)
      omega
  rw [heq] at hdegree
  exact BooleanDegree.or_requires_degree hdegree

end SparseMM.AggregationLower
