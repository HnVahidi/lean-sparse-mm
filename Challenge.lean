module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Independent advertised statements and concrete model

Source: Gupta, Suomela, and Vahidi, *Sparse Matrix Multiplication Exponent 1.5
in the Low-bandwidth Model*, supplied 10-page PDF, SHA-256
37ff1c413e7b088bf4364e64c8886128e5fbc566e3abebb6a59c5c2a79e42672.

Theorem 4 is encoded as one public local-state distributed program, chosen
before numerical matrices, correct at its balanced output holders. Every
stage uses the concrete single-send/single-receive operational semantics below.
Messages carry one semiring value. The separate wire theorem removes public
labels and preserves any lossless encoding of values actually transmitted;
the paper's O(log n)-bit encoding premise is not manufactured from a semiring.

Integral teams use floor-sqrt(d)+1. Output balancing uses public batch
permutations; the main algorithm's routing uses 2D rounds. Exact regular-load
D-round redistribution (Lemma 3) is proved separately below. The output
assignment is an alternative to the source's exact cyclic construction.
Deliberate holes below are statement placeholders, never imported by Solution.
-/

open scoped BigOperators

universe u

namespace SparseMM

abbrev Mask (n : ℕ) := Finset (Fin n × Fin n)

def rowMask {n : ℕ} (A : Mask n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i, j) ∈ A

def colMask {n : ℕ} (A : Mask n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (i, j) ∈ A

def UniformSparse {n : ℕ} (A : Mask n) (d : ℕ) : Prop :=
  (∀ i, (rowMask A i).card ≤ d) ∧ (∀ j, (colMask A j).card ≤ d)

/-- Middle indices contributing to one requested position. -/
def middleSet {n : ℕ} (A B : Mask n) (p : Fin n × Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => (p.1, j) ∈ A ∧ (j, p.2) ∈ B

/-- Clustered outputs have zero weight in the residual phase. -/
def residualWeight {n : ℕ} (A B R : Mask n) (p : Fin n × Fin n) : ℕ :=
  if p ∈ R then (middleSet A B p).card else 0

def teamSize (d : ℕ) : ℕ := Nat.sqrt d + 1

def threshold (d : ℕ) : ℕ := d * teamSize d

theorem threshold_le_two_mul_sqrt {d : ℕ} (hd : 0 < d) :
    (threshold d : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt d := by
  sorry

end SparseMM

namespace SparseMM.Counting

def load {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (weight : Job → ℕ) (node : Node) : ℕ :=
  ∑ j, if owner j = node then weight j else 0

def count {Job Node : Type*} [Fintype Job] [DecidableEq Node]
    (owner : Job → Node) (node : Node) : ℕ :=
  (Finset.univ.filter fun j => owner j = node).card

end SparseMM.Counting

namespace SparseMM.Algebra
variable {I J K T R : Type*}

/-- Every input coordinate outside its allowed input mask contains zero.
Marked coordinates are allowed to contain zero as well. -/
def SupportedBy [Zero R] (A : Matrix I J R) (mask : Finset (I × J)) : Prop :=
  ∀ i j, (i, j) ∉ mask → A i j = 0

end SparseMM.Algebra

namespace SparseMM.HelperPlan

abbrev Input {n : ℕ} (A B : Mask n) :=
  Sum {e // e ∈ A} {e // e ∈ B}

end SparseMM.HelperPlan

namespace SparseMM.Routing

/-- A slot assignment obeys both directed port constraints. -/
def LegalOn {Packet Node : Type*} {rounds : ℕ}
    (packets : Finset Packet) (source destination : Packet → Node)
    (slot : Packet → Fin rounds) : Prop :=
  ∀ p ∈ packets, ∀ q ∈ packets, slot p = slot q →
    (source p = source q ∨ destination p = destination q) → p = q

end SparseMM.Routing

namespace SparseMM

variable {I K : Type*} [DecidableEq I] [DecidableEq K]

/-- A set of requested coordinates contained in at most `d` rows and columns. -/
def FitsRectangle (d : ℕ) (C : Finset (I × K)) : Prop :=
  ∃ rows : Finset I, ∃ cols : Finset K,
    rows.card ≤ d ∧ cols.card ≤ d ∧ C ⊆ rows ×ˢ cols

/-- Every rectangle with at most `d` rows and columns contains fewer than `t`
remaining requested coordinates. -/
def ResidualSparse (d t : ℕ) (R : Finset (I × K)) : Prop :=
  ∀ rows : Finset I, ∀ cols : Finset K,
    rows.card ≤ d → cols.card ≤ d → (R ∩ rows ×ˢ cols).card < t

/-- The complete finite certificate produced by dense-rectangle extraction.
The `accounting` field includes the residual, so the cluster count cannot hide
overlaps or discarded output positions. -/
structure Clustering (Q : Finset (I × K)) (d t : ℕ) where
  clusters : List (Finset (I × K))
  residual : Finset (I × K)
  cluster_sub : ∀ C ∈ clusters, C ⊆ Q
  cluster_card : ∀ C ∈ clusters, C.card = t
  cluster_rectangle : ∀ C ∈ clusters, FitsRectangle d C
  pairwise_disjoint : clusters.Pairwise Disjoint
  residual_sub : residual ⊆ Q
  residual_disjoint : ∀ C ∈ clusters, Disjoint C residual
  cover : ∀ p, p ∈ Q ↔ p ∈ residual ∨ ∃ C ∈ clusters, p ∈ C
  sparse : ResidualSparse d t residual
  accounting : clusters.length * t + residual.card = Q.card

/-- Complete finite clustering from public requested coordinates. -/

theorem exists_clustering (Q : Finset (I × K)) (d t : ℕ) (ht : 0 < t) :
    Nonempty (Clustering Q d t) := by
  sorry

end SparseMM


namespace SparseMM

/-- Literal strict residual-output load guarantee, with an actual fixed assignment. -/

theorem exists_strict_output_plan {n d t : ℕ} (hn : 0 < n)
    (A B Q R : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hQ : UniformSparse Q d) (hRQ : R ⊆ Q) (hs : ResidualSparse d t R) :
    ∃ out : {p // p ∈ Q} → Fin n,
      (∀ node, Counting.count out node ≤ d) ∧
      (∀ node, Counting.load out (fun q => residualWeight A B R q.val) node < t + d) := by
  sorry

end SparseMM


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

theorem executeFrom_delivers (plan : StaticPlan source destination rounds)
    (state : Configuration Packet Node Value) (values : Packet → Value)
    (hvalue : ∀ p, state (source p) p = some (values p)) (p : Packet) :
    executeFrom plan rounds state (destination p) p = some (values p) := by
  sorry

theorem exists_public_redistribution (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card ≤ D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card ≤ D) :
    ∃ plan : StaticPlan source destination (2 * D),
      ∀ (values : Packet → Value) (p : Packet),
        execute plan values (2 * D) (destination p) p = some (values p) := by
  sorry

/-- Packet labels of actual outgoing numerical messages in one round. -/
def transmitted (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) : Finset Packet := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ value, send plan time (source p) (state (source p)) = some (p, value)

omit [DecidableEq Packet] in

theorem actual_send_capacity (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) (node : Node) :
    ((transmitted plan time state).filter (fun p => source p = node)).card ≤ 1 := by
  sorry

omit [DecidableEq Packet] in

theorem actual_receive_capacity (plan : StaticPlan source destination rounds) (time : ℕ)
    (state : Configuration Packet Node Value) (node : Node) :
    ((transmitted plan time state).filter (fun p => destination p = node)).card ≤ 1 := by
  sorry

end
end Execution
end SparseMM.Model


namespace SparseMM.ExactRouting
variable {Packet Node : Type*} [DecidableEq Packet] [DecidableEq Node] [Fintype Node]

/-- The source's exact regular-load redistribution schedule (Lemma 3). -/

theorem exists_schedule [Fintype Packet] (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card = D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card = D) :
    ∃ slot : Packet → Fin D, Routing.LegalOn Finset.univ source destination slot := by
  sorry

theorem exists_public_redistribution [Fintype Packet] {Value : Type*}
    (source destination : Packet → Node) (D : ℕ)
    (hout : ∀ node, (Finset.univ.filter (fun p => source p = node)).card = D)
    (hin : ∀ node, (Finset.univ.filter (fun p => destination p = node)).card = D) :
    ∃ plan : Model.StaticPlan source destination D,
      ∀ (values : Packet → Value) (p : Packet),
        Model.execute plan values D (destination p) p = some (values p) := by
  sorry

end SparseMM.ExactRouting


namespace SparseMM.LocalPipeline

/-- A public phase. Numerical messages are prepared from the sender's own
state, and the receiver combines its own old state with its delivered memory.
The packet labels and routes are fixed before private values are supplied. -/
structure Stage (Node State Value : Type*) [DecidableEq Node] where
  Packet : Type
  packetFinite : Fintype Packet
  packetDecEq : DecidableEq Packet
  source : Packet → Node
  destination : Packet → Node
  rounds : ℕ
  plan : @Model.StaticPlan Packet Node packetFinite source destination rounds
  prepare : Node → State → Model.LocalState Packet Value
  collect : Node → State → Model.LocalState Packet Value → State

noncomputable def Stage.run {Node State Value : Type*} [DecidableEq Node]
    (stage : Stage Node State Value) (state : Node → State) : Node → State := by
  letI := stage.packetFinite
  letI := stage.packetDecEq
  exact fun node => stage.collect node (state node)
    (Model.executeFrom stage.plan stage.rounds
      (fun sender => stage.prepare sender (state sender)) node)

/-- A finite distributed program whose every inter-node operation is one of
the verified static redistributions. Initialization and output are local. -/
structure Program (Node View State Value Output : Type*) [DecidableEq Node] where
  init : Node → View → State
  stages : List (Stage Node State Value)
  finish : Node → State → Output

def Program.rounds {Node View State Value Output : Type*} [DecidableEq Node]
    (program : Program Node View State Value Output) : ℕ :=
  (program.stages.map Stage.rounds).sum

noncomputable def Program.execute {Node View State Value Output : Type*}
    [DecidableEq Node] (program : Program Node View State Value Output)
    (views : Node → View) : Node → State :=
  program.stages.foldl (fun state stage => stage.run state)
    (fun node => program.init node (views node))

noncomputable def Program.output {Node View State Value Output : Type*}
    [DecidableEq Node] (program : Program Node View State Value Output)
    (views : Node → View) (node : Node) : Output :=
  program.finish node (program.execute views node)

end SparseMM.LocalPipeline


namespace SparseMM.Computation
variable {n : ℕ} {A B : Mask n} {S : Type*} [Semiring S]

/-- The mathematical value carried by one allowed input record. -/
def inputValue (U V : Matrix (Fin n) (Fin n) S) (e : HelperPlan.Input A B) : S :=
  match e with
  | Sum.inl a => U a.val.1 a.val.2
  | Sum.inr b => V b.val.1 b.val.2

end SparseMM.Computation


namespace SparseMM.SupportedProgram
variable {n : ℕ} {A B : Mask n} {S : Type*} [Semiring S]

abbrev View (A B : Mask n) (S : Type*) := Model.LocalState (HelperPlan.Input A B) S

noncomputable section

/-- The mathematical input instance supplies each numerical entry only to its
actual public original holder. -/
def views (original : HelperPlan.Input A B → Fin n) (U V : Matrix (Fin n) (Fin n) S) (node : Fin n) : View A B S :=
  fun e => if original e = node then some (Computation.inputValue U V e) else none

end
end SparseMM.SupportedProgram


namespace SparseMM.OutputAssignment

/-- The actual weighted load received by a machine under an assignment. -/
def weightedLoad {Job : Type*} [Fintype Job] {n : ℕ}
    (weights : Job → ℕ) (assignment : Job → Fin n) (i : Fin n) : ℕ :=
  ∑ x : Job, if assignment x = i then weights x else 0

/-- The actual number of assigned slots, independent of their weights. -/
def assignedCount {Job : Type*} [Fintype Job] {n : ℕ}
    (assignment : Job → Fin n) (i : Fin n) : ℕ :=
  ∑ x : Job, if assignment x = i then 1 else 0

/-- One public assignment balances counts and weighted contributions. -/

theorem exists_balanced_output_assignment {Job : Type*} [Fintype Job]
    (n d W : ℕ) (weights : Job → ℕ)
    (hcard : Fintype.card Job ≤ n * d) (hw : ∀ x, weights x ≤ W) :
    ∃ assignment : Job → Fin n,
      (∀ i : Fin n, assignedCount assignment i ≤ d) ∧
      ∀ i : Fin n, n * weightedLoad weights assignment i ≤
        (∑ x : Job, weights x) + n * W := by
  sorry

end SparseMM.OutputAssignment


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

theorem receive_eq_model (plan : Model.StaticPlan source destination rounds)
    (time : ℕ) (node : Node) (state : Model.Configuration Packet Node Value) :
    receive plan time node state = Model.receive plan time node state := by
  sorry

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

theorem encodedReceive_eq_model (encode : Value → Code) (decode : Code → Value)
    (plan : Model.StaticPlan source destination rounds) (time : ℕ) (node : Node)
    (state : Model.Configuration Packet Node Value)
    (hcodec : ∀ sender value, send plan time sender (state sender) = some value →
      decode (encode value) = value) :
    encodedReceive encode decode plan time node state = Model.receive plan time node state := by
  sorry

end
end SparseMM.Wire


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

/-- Robust broadcast influence lower bound, including adaptive addressing and silence. -/

theorem broadcast_requires_rounds (source : Fin n) (left right : Fin n → State)
    (hlocal : ∀ node, node ≠ source → left node = right node) (time : ℕ)
    (hfalse : ∀ node, system.output node (system.execute left time node) = false)
    (htrue : ∀ node, system.output node (system.execute right time node) = true) :
    n ≤ 3 ^ time := by
  sorry

end System
end SparseMM.BroadcastLower


namespace SparseMM.Signatures

def StaticPlan_constructor := @Model.StaticPlan.mk
def Stage_constructor := @LocalPipeline.Stage.mk
def Program_constructor := @LocalPipeline.Program.mk
def Clustering_constructor := @Clustering.mk
def BroadcastSystem_constructor := @BroadcastLower.System.mk

end SparseMM.Signatures

namespace SparseMM

/-- Theorem 4: one public program works for all supported numerical inputs. -/

theorem supported_sparse_mm {n d K : ℕ} (hn : 0 < n) (hd : 0 < d)
    (A B Q : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hQ : UniformSparse Q d) (original : HelperPlan.Input A B → Fin n)
    (horiginal : ∀ node, Counting.count original node ≤ K * d)
    (S : Type u) [Semiring S] :
    ∃ out : {p // p ∈ Q} → Fin n, ∃ State : Type u,
      ∃ code : LocalPipeline.Program (Fin n) (HelperPlan.Input A B → Option S)
          State S ({p // p ∈ Q} → S),
        (∀ node, Counting.count out node ≤ d) ∧
        code.rounds ≤ (4 * K + 40) * threshold d ∧
        (code.rounds : ℝ) ≤ (8 * K + 80) * (d : ℝ) * Real.sqrt d ∧
        ∀ U V : Matrix (Fin n) (Fin n) S,
          Algebra.SupportedBy U A → Algebra.SupportedBy V B →
          ∀ q : {p // p ∈ Q},
            code.output (SupportedProgram.views original U V) (out q) q =
              (U * V) q.val.1 q.val.2 := by
  sorry

end SparseMM

namespace SparseMM.BooleanDegree
abbrev Cube (n : ℕ) := Fin n → Bool
end SparseMM.BooleanDegree


namespace SparseMM.AggregationLower
open BooleanDegree
variable {n : ℕ} {State Message : Type*}

/-- Each processor's initial private state depends only on its own input bit. -/
def initialConfiguration (initial : Fin n → Bool → State) (x : Cube n) : Fin n → State :=
  fun node => initial node (x node)

/-- All-input legality and local private initial states force logarithmic OR aggregation. -/

theorem or_requires_rounds (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ) (receiver : Fin n)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time))
    (hcorrect : ∀ x : Cube n, system.output receiver
      (system.execute (initialConfiguration initial x) T receiver) = decide (∃ i, x i = true)) :
    n ≤ 2 ^ T := by
  sorry

theorem and_requires_rounds (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ) (receiver : Fin n)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time))
    (hcorrect : ∀ x : Cube n, system.output receiver
      (system.execute (initialConfiguration initial x) T receiver) = decide (∀ i, x i = true)) :
    n ≤ 2 ^ T := by
  sorry

theorem sum_requires_rounds (system : BroadcastLower.System n State Message)
    (initial : Fin n → Bool → State) (T : ℕ) (receiver : Fin n)
    (readSum : State → ℕ)
    (hlegal : ∀ time < T, ∀ x : Cube n,
      system.LegalAt time (system.execute (initialConfiguration initial x) time))
    (hcorrect : ∀ x : Cube n, readSum
      (system.execute (initialConfiguration initial x) T receiver) =
        ∑ i : Fin n, if x i then 1 else 0) :
    n ≤ 2 ^ T := by
  sorry

end SparseMM.AggregationLower


namespace SparseMM.ToolboxComplexity

theorem log_div_le_rounds {n base T : ℕ} (hn : 0 < n) (hbase : 2 ≤ base)
    (hbound : n ≤ base ^ T) :
    Real.log (n : ℝ) / Real.log (base : ℝ) ≤ (T : ℝ) := by
  sorry

theorem clog_two_le_log_div_add_one {n : ℕ} (hn : 0 < n) :
    (Nat.clog 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
  sorry

theorem pipeline_rounds_le {n k : ℕ} (hn : 0 < n) :
    ((2 * k + 2 * Nat.clog 2 n : ℕ) : ℝ) ≤
      2 * (k : ℝ) + (2 / Real.log 2) * Real.log (n : ℝ) + 2 := by
  sorry

theorem single_value_rounds_le_log {n : ℕ} (hn : 2 ≤ n) :
    ((2 + 2 * Nat.clog 2 n : ℕ) : ℝ) ≤
      (6 / Real.log 2) * Real.log (n : ℝ) := by
  sorry

end SparseMM.ToolboxComplexity


namespace SparseMM.PipelinedBroadcast

/-- One public local scalar system broadcasts every private source vector. -/

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
  sorry

end SparseMM.PipelinedBroadcast

namespace SparseMM.PipelinedAggregation

/-- One public local scalar system aggregates every privately distributed vector. -/

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
  sorry

end SparseMM.PipelinedAggregation


namespace SparseMM.BooleanAggregation

/-- Boolean AND aggregation with literal Boolean messages and private local inputs. -/

theorem exists_and {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∃ NodeState : Type, ∃ code : BroadcastLower.System n NodeState Bool,
      ∃ init : Fin n → (Fin k → Bool) → NodeState,
      ∃ readout : Fin n → NodeState → Fin k → Bool,
        (∀ time node state message, code.send time node state ≠ some (node, message)) ∧
        ∀ bits : Fin n → Fin k → Bool,
          (∀ time, code.LegalAt time (code.execute (fun node => init node (bits node)) time)) ∧
          ∀ r, readout ⟨0, hn⟩ (code.execute (fun node => init node (bits node))
            (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r = decide (∀ node, bits node r = true) := by
  sorry

/-- Boolean OR aggregation with literal Boolean messages and private local inputs. -/

theorem exists_or {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∃ NodeState : Type, ∃ code : BroadcastLower.System n NodeState Bool,
      ∃ init : Fin n → (Fin k → Bool) → NodeState,
      ∃ readout : Fin n → NodeState → Fin k → Bool,
        (∀ time node state message, code.send time node state ≠ some (node, message)) ∧
        ∀ bits : Fin n → Fin k → Bool,
          (∀ time, code.LegalAt time (code.execute (fun node => init node (bits node)) time)) ∧
          ∀ r, readout ⟨0, hn⟩ (code.execute (fun node => init node (bits node))
            (2 * k + 2 * Nat.clog 2 n) ⟨0, hn⟩) r = decide (∃ node, bits node r = true) := by
  sorry

end SparseMM.BooleanAggregation
