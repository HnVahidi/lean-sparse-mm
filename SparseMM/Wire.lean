module

public import SparseMM.Model

@[expose] public section

/-!
# One-value wire messages

Packet labels in the operational proof are local addresses. The public
schedule determines the incoming label, so a physical sender need transmit
only the value. An injective representation is needed only for the values
that are actually sent, not for every element of an arbitrary semiring.
-/

namespace SparseMM.Wire

variable {Packet Node Value Code : Type*} [Fintype Packet]
    [DecidableEq Packet] [DecidableEq Node]
    {source destination : Packet → Node} {rounds : ℕ}

noncomputable section

/-- The physical payload drops the public packet label. -/
def send (plan : Model.StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (memory : Model.LocalState Packet Value) : Option Value :=
  (Model.send plan time node memory).map Prod.snd

/-- A receiver reconstructs the local packet address from public code. -/
def receive (plan : Model.StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state : Model.Configuration Packet Node Value) : Option (Packet × Value) :=
  (Model.incomingLabel plan time node).bind fun p =>
    (send plan time (source p) (state (source p))).map fun value => (p, value)

/-- Omitting packet labels on the wire leaves the operational messages exactly
unchanged, for every configuration, including missing source values. -/
theorem receive_eq_model (plan : Model.StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (state : Model.Configuration Packet Node Value) :
    receive plan time node state = Model.receive plan time node state := by
  unfold receive Model.receive send
  cases hi : Model.incomingLabel plan time node with
  | none => simp
  | some p =>
      simp only [Option.bind_some]
      cases hs : Model.send plan time (source p) (state (source p)) with
      | none => simp
      | some message =>
          obtain ⟨q, value⟩ := message
          have hq := Model.outgoingLabel_spec plan time (source p) q
            (Model.send_spec plan time (source p) (state (source p)) q value hs).1
          have hp := Model.incomingLabel_spec plan time node p hi
          have heq : q = p := plan.legal q (Finset.mem_univ _) p (Finset.mem_univ _)
            (Fin.ext (hq.1.trans hp.1.symm)) (Or.inl hq.2.1)
          subst q
          simp

/-- Encode the one-value physical payload using any chosen wire alphabet. -/
def encodedSend (encode : Value → Code)
    (plan : Model.StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (memory : Model.LocalState Packet Value) : Option Code :=
  (send plan time node memory).map encode

/-- Decode the physical payload, then reconstruct the public packet address. -/
def encodedReceive (encode : Value → Code) (decode : Code → Value)
    (plan : Model.StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state : Model.Configuration Packet Node Value) : Option (Packet × Value) :=
  (Model.incomingLabel plan time node).bind fun p =>
    ((encodedSend encode plan time (source p) (state (source p))).map decode).map
      fun value => (p, value)

/-- Exact decoding is required only on the values actually emitted in this
round. Under that premise the coded wire has exactly the verified semantics. -/
theorem encodedReceive_eq_model (encode : Value → Code) (decode : Code → Value)
    (plan : Model.StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state : Model.Configuration Packet Node Value)
    (hcodec : ∀ sender value, send plan time sender (state sender) = some value →
      decode (encode value) = value) :
    encodedReceive encode decode plan time node state = Model.receive plan time node state := by
  rw [← receive_eq_model]
  unfold encodedReceive receive encodedSend
  cases hi : Model.incomingLabel plan time node with
  | none => simp
  | some p =>
      simp only [Option.bind_some]
      cases hs : send plan time (source p) (state (source p)) with
      | none => simp
      | some value => simp [hcodec (source p) value hs]

end

end SparseMM.Wire
