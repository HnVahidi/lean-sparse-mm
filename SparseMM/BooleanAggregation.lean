module

public import SparseMM.PipelinedBroadcast

@[expose] public section

namespace SparseMM.BooleanAggregation

open scoped BigOperators

noncomputable def mapMessage {n : ℕ} {State Message NewMessage : Type*}
    (code : BroadcastLower.System n State Message) (equiv : Message ≃ NewMessage) :
    BroadcastLower.System n State NewMessage where
  send := fun time node state => (code.send time node state).map
    (fun message => (message.1, equiv message.2))
  update := fun time node state inbox => code.update time node state
    (fun sender => (inbox sender).map equiv.symm)
  output := code.output

theorem mapped_inbox {n : ℕ} {State Message NewMessage : Type*}
    (code : BroadcastLower.System n State Message) (equiv : Message ≃ NewMessage)
    (time : ℕ) (state : Fin n → State) (receiver sender : Fin n) :
    (mapMessage code equiv).inbox time state receiver sender =
      (code.inbox time state receiver sender).map equiv := by
  classical
  unfold BroadcastLower.System.inbox mapMessage
  cases hs : code.send time sender (state sender) with
  | none => simp [hs]
  | some message =>
      obtain ⟨destination, value⟩ := message
      by_cases hd : destination = receiver <;> simp [hs, hd]

theorem mapped_step {n : ℕ} {State Message NewMessage : Type*}
    (code : BroadcastLower.System n State Message) (equiv : Message ≃ NewMessage)
    (time : ℕ) (state : Fin n → State) :
    (mapMessage code equiv).step time state = code.step time state := by
  funext node
  simp only [BroadcastLower.System.step]
  change code.update time node (state node)
    (fun sender => ((mapMessage code equiv).inbox time state node sender).map equiv.symm) = _
  have hinbox : (fun sender => ((mapMessage code equiv).inbox time state node sender).map equiv.symm) =
      code.inbox time state node := by
    funext sender
    rw [mapped_inbox]
    cases code.inbox time state node sender <;> simp
  rw [hinbox]

theorem mapped_execute {n : ℕ} {State Message NewMessage : Type*}
    (code : BroadcastLower.System n State Message) (equiv : Message ≃ NewMessage)
    (initial : Fin n → State) (time : ℕ) :
    (mapMessage code equiv).execute initial time = code.execute initial time := by
  induction time with
  | zero => rfl
  | succ time ih => rw [BroadcastLower.System.execute, ih, mapped_step]; rfl

theorem mapped_legal {n : ℕ} {State Message NewMessage : Type*}
    (code : BroadcastLower.System n State Message) (equiv : Message ≃ NewMessage)
    (time : ℕ) (state : Fin n → State) (h : code.LegalAt time state) :
    (mapMessage code equiv).LegalAt time state := by
  classical
  intro receiver
  simpa only [BroadcastLower.System.LegalAt, mapped_inbox, Option.isSome_map] using h receiver

theorem mapped_no_self {n : ℕ} {State Message NewMessage : Type*}
    (code : BroadcastLower.System n State Message) (equiv : Message ≃ NewMessage)
    (h : ∀ time node state message, code.send time node state ≠ some (node, message)) :
    ∀ time node state message, (mapMessage code equiv).send time node state ≠ some (node, message) := by
  intro time node state message he
  obtain ⟨original, horiginal, he⟩ := Option.map_eq_some_iff.mp he
  have hnode : original.1 = node := congrArg Prod.fst he
  apply h time node state original.2
  simpa only [← hnode] using horiginal

structure AllBit where
  value : Bool
  deriving DecidableEq

namespace AllBit

theorem ext {a b : AllBit} (h : a.value = b.value) : a = b := by
  cases a with
  | mk a => cases b with
    | mk b => exact congrArg AllBit.mk h

instance : Zero AllBit := ⟨⟨true⟩⟩
instance : Add AllBit := ⟨fun a b => ⟨a.value && b.value⟩⟩

@[simp] theorem value_zero : (0 : AllBit).value = true := rfl
@[simp] theorem value_add (a b : AllBit) : (a + b).value = (a.value && b.value) := rfl

instance : AddCommMonoid AllBit where
  add_assoc a b c := by apply AllBit.ext; exact Bool.and_assoc _ _ _
  zero_add a := by apply AllBit.ext; exact Bool.true_and _
  add_zero a := by apply AllBit.ext; exact Bool.and_true _
  add_comm a b := by apply AllBit.ext; exact Bool.and_comm _ _
  nsmul := nsmulRec

theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    (∑ i ∈ s, AllBit.mk (f i)).value = decide (∀ i ∈ s, f i = true) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, ih, forall_eq_or_imp]

end AllBit

structure AnyBit where
  value : Bool
  deriving DecidableEq

namespace AnyBit

theorem ext {a b : AnyBit} (h : a.value = b.value) : a = b := by
  cases a with
  | mk a => cases b with
    | mk b => exact congrArg AnyBit.mk h

instance : Zero AnyBit := ⟨⟨false⟩⟩
instance : Add AnyBit := ⟨fun a b => ⟨a.value || b.value⟩⟩

@[simp] theorem value_zero : (0 : AnyBit).value = false := rfl
@[simp] theorem value_add (a b : AnyBit) : (a + b).value = (a.value || b.value) := rfl

instance : AddCommMonoid AnyBit where
  add_assoc a b c := by apply AnyBit.ext; exact Bool.or_assoc _ _ _
  zero_add a := by apply AnyBit.ext; exact Bool.false_or _
  add_zero a := by apply AnyBit.ext; exact Bool.or_false _
  add_comm a b := by apply AnyBit.ext; exact Bool.or_comm _ _
  nsmul := nsmulRec

theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    (∑ i ∈ s, AnyBit.mk (f i)).value = decide (∃ i ∈ s, f i = true) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert ha, ih]

end AnyBit

theorem pipelined_and {n k : ℕ} (hn : 0 < n) (bits : Fin n → Fin k → Bool) (r : Fin k) :
    (PipelinedAggregation.execute (fun node r => AllBit.mk (bits node r))
      (PipelinedBroadcast.rounds n k) (PipelinedBroadcast.root hn) r).value =
        decide (∀ node, bits node r = true) := by
  classical
  rw [PipelinedAggregation.aggregates hn]
  simpa using AllBit.value_sum Finset.univ (fun node => bits node r)

theorem pipelined_or {n k : ℕ} (hn : 0 < n) (bits : Fin n → Fin k → Bool) (r : Fin k) :
    (PipelinedAggregation.execute (fun node r => AnyBit.mk (bits node r))
      (PipelinedBroadcast.rounds n k) (PipelinedBroadcast.root hn) r).value =
        decide (∃ node, bits node r = true) := by
  classical
  rw [PipelinedAggregation.aggregates hn]
  simpa using AnyBit.value_sum Finset.univ (fun node => bits node r)

theorem pipelined_sum {n k : ℕ} (hn : 0 < n) (bits : Fin n → Fin k → Bool) (r : Fin k) :
    PipelinedAggregation.execute (fun node r => if bits node r then (1 : ℕ) else 0)
      (PipelinedBroadcast.rounds n k) (PipelinedBroadcast.root hn) r =
        ∑ node, if bits node r then 1 else 0 :=
  PipelinedAggregation.aggregates hn _ r

/-- All partial sums in Boolean counting fit in the range `0..n`, throughout
the execution, so the sum specialization uses logarithmically many bits. -/
theorem sum_accumulator_le {n k : ℕ} (bits : Fin n → Fin k → Bool)
    (time : ℕ) (node : Fin n) (r : Fin k) :
    PipelinedAggregation.execute (fun node r => if bits node r then (1 : ℕ) else 0)
      time node r ≤ n := by
  calc
    _ ≤ ∑ other, PipelinedAggregation.execute
        (fun node r => if bits node r then (1 : ℕ) else 0) time other r :=
      Finset.single_le_sum (fun other _ => Nat.zero_le _) (Finset.mem_univ node)
    _ = ∑ other : Fin n, if bits other r then 1 else 0 :=
      PipelinedAggregation.execute_conserves _ time r
    _ ≤ ∑ _other : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro other _
      split_ifs <;> omega
    _ = n := by simp

def allBitEquiv : AllBit ≃ Bool where
  toFun := AllBit.value
  invFun := AllBit.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

def anyBitEquiv : AnyBit ≃ Bool where
  toFun := AnyBit.value
  invFun := AnyBit.mk
  left_inv a := by cases a; rfl
  right_inv _ := rfl

/-- Pipelined Boolean AND with literal one-bit messages and source-local input. -/
theorem exists_and {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∃ NodeState : Type, ∃ code : BroadcastLower.System n NodeState Bool,
      ∃ init : Fin n → (Fin k → Bool) → NodeState,
      ∃ readout : Fin n → NodeState → Fin k → Bool,
        (∀ time node state message, code.send time node state ≠ some (node, message)) ∧
        ∀ bits : Fin n → Fin k → Bool,
          (∀ time, code.LegalAt time (code.execute (fun node => init node (bits node)) time)) ∧
          ∀ r, readout ⟨0, hn⟩ (code.execute (fun node => init node (bits node))
            (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r = decide (∀ node, bits node r = true) := by
  classical
  obtain ⟨NodeState, code, init, readout, hself, hcorrect⟩ :=
    PipelinedAggregation.exists_aggregation hn k AllBit
  refine ⟨NodeState, mapMessage code allBitEquiv,
    fun node bits => init node (fun r => AllBit.mk (bits r)),
    fun node state r => (readout node state r).value,
    mapped_no_self code allBitEquiv
      (fun time node state message he => hself time node state node message he rfl), ?_⟩
  intro bits
  obtain ⟨hlegal, hread⟩ := hcorrect (fun node r => AllBit.mk (bits node r))
  constructor
  · intro time
    rw [mapped_execute]
    exact mapped_legal _ _ _ _ (hlegal time)
  · intro r
    rw [mapped_execute]
    change (readout ⟨0, hn⟩ (code.execute
      (fun node => init node (fun r => AllBit.mk (bits node r)))
      (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r).value = _
    rw [hread]
    simpa using AllBit.value_sum Finset.univ (fun node => bits node r)

/-- Pipelined Boolean OR with literal one-bit messages and source-local input. -/
theorem exists_or {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∃ NodeState : Type, ∃ code : BroadcastLower.System n NodeState Bool,
      ∃ init : Fin n → (Fin k → Bool) → NodeState,
      ∃ readout : Fin n → NodeState → Fin k → Bool,
        (∀ time node state message, code.send time node state ≠ some (node, message)) ∧
        ∀ bits : Fin n → Fin k → Bool,
          (∀ time, code.LegalAt time (code.execute (fun node => init node (bits node)) time)) ∧
          ∀ r, readout ⟨0, hn⟩ (code.execute (fun node => init node (bits node))
            (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r = decide (∃ node, bits node r = true) := by
  classical
  obtain ⟨NodeState, code, init, readout, hself, hcorrect⟩ :=
    PipelinedAggregation.exists_aggregation hn k AnyBit
  refine ⟨NodeState, mapMessage code anyBitEquiv,
    fun node bits => init node (fun r => AnyBit.mk (bits r)),
    fun node state r => (readout node state r).value,
    mapped_no_self code anyBitEquiv
      (fun time node state message he => hself time node state node message he rfl), ?_⟩
  intro bits
  obtain ⟨hlegal, hread⟩ := hcorrect (fun node r => AnyBit.mk (bits node r))
  constructor
  · intro time
    rw [mapped_execute]
    exact mapped_legal _ _ _ _ (hlegal time)
  · intro r
    rw [mapped_execute]
    change (readout ⟨0, hn⟩ (code.execute
      (fun node => init node (fun r => AnyBit.mk (bits node r)))
      (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r).value = _
    rw [hread]
    simpa using AnyBit.value_sum Finset.univ (fun node => bits node r)

end SparseMM.BooleanAggregation
