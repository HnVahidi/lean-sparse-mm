module

public import SparseMM.Model

@[expose] public section

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

/-- A phase is compatible with a specified mathematical packet value when
that value can be prepared from the source's current local state. -/
theorem Stage.delivers {Node State Value : Type*} [DecidableEq Node]
    (stage : Stage Node State Value) (state : Node → State)
    (values : stage.Packet → Value)
    (hvalues : ∀ p, stage.prepare (stage.source p) (state (stage.source p)) p =
      some (values p)) (p : stage.Packet) :
    letI := stage.packetFinite
    letI := stage.packetDecEq
    Model.executeFrom stage.plan stage.rounds
      (fun node => stage.prepare node (state node)) (stage.destination p) p =
      some (values p) := by
  let _ := stage.packetFinite
  let _ := stage.packetDecEq
  exact Model.executeFrom_delivers stage.plan _ values hvalues p

end SparseMM.LocalPipeline
