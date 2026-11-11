module

public import SparseMM.Plan
public import SparseMM.Computation
public import SparseMM.LocalPipeline

/-!
# The five-phase supported sparse-multiplication program

Public code comes from `Plan`. Every message is prepared from its sender's
own state, and every numerical arithmetic operation reads a local memory.
Global matrices occur only in the specification and correctness proofs.
-/

@[expose] public section

set_option maxHeartbeats 1200000

namespace SparseMM.SupportedProgram

variable {n d K : ℕ} {A B Q : Mask n}
variable {original : HelperPlan.Input A B → Fin n}
variable {S : Type*} [Semiring S]

abbrev Request (P : Plan (d := d) (K := K) A B Q original) :=
  HelperPlan.Request A B P.decomposition

abbrev Needed (P : Plan (d := d) (K := K) A B Q original) :=
  Multicast.Needed (HelperPlan.Request.input (A := A) (B := B) (D := P.decomposition))

abbrev PartialPacket (P : Plan (d := d) (K := K) A B Q original) :=
  PartialDelivery.Packet (h := teamSize d) P.decomposition

abbrev ResidualPacket (P : Plan (d := d) (K := K) A B Q original) :=
  ResidualDelivery.Packet A B Q P.decomposition.residual

/-- A processor retains its original inputs and the separate memories filled
by each communication phase. No field contains a global matrix. -/
structure State (P : Plan (d := d) (K := K) A B Q original) (S : Type*) where
  originalInputs : Model.LocalState (HelperPlan.Input A B) S
  broadcastInputs : Model.LocalState (Needed P) S
  requests : Model.LocalState (Request P) S
  partials : Model.LocalState (PartialPacket P) S
  middleInputs : Model.LocalState (HelperPlan.Input A B) S
  products : Model.LocalState (ResidualPacket P) S

abbrev View (A B : Mask n) (S : Type*) := Model.LocalState (HelperPlan.Input A B) S

noncomputable section

variable (P : Plan (d := d) (K := K) A B Q original)

def initState (_node : Fin n) (view : View A B S) : State P S where
  originalInputs := view
  broadcastInputs := fun _ => none
  requests := fun _ => none
  partials := fun _ => none
  middleInputs := fun _ => none
  products := fun _ => none

/-- Original holders send one copy of each needed input to its broadcaster. -/
def firstStage : LocalPipeline.Stage (Fin n) (State P S) S where
  Packet := Needed P
  packetFinite := inferInstance
  packetDecEq := inferInstance
  source := fun e => original e.val
  destination := fun e => P.broadcaster e.val
  rounds := 2 * max (K * d) (4 * threshold d + d)
  plan := P.first
  prepare := fun _ state e => state.originalInputs e.val
  collect := fun _ state delivered => {state with broadcastInputs := delivered}

/-- Broadcasters copy their locally received inputs to the requesting helpers. -/
def secondStage : LocalPipeline.Stage (Fin n) (State P S) S where
  Packet := Request P
  packetFinite := inferInstance
  packetDecEq := inferInstance
  source := P.broadcaster ∘ HelperPlan.Request.input
  destination := P.place ∘ HelperPlan.Request.helper P.assignment
  rounds := 2 * (4 * threshold d + d)
  plan := P.second
  prepare := fun _ state r => state.broadcastInputs
    ⟨r.input, Multicast.request_needed _ r⟩
  collect := fun _ state delivered => {state with requests := delivered}

/-- Helpers compute partial sums from their received requests and deliver them. -/
def partialStage : LocalPipeline.Stage (Fin n) (State P S) S where
  Packet := PartialPacket P
  packetFinite := inferInstance
  packetDecEq := inferInstance
  source := P.place ∘ PartialDelivery.helper P.decomposition
  destination := PartialDelivery.destination P.decomposition P.out
  rounds := 2 * (threshold d + d * teamSize d)
  plan := P.«partial»
  prepare := fun _ state p => some
    (Computation.computePartial P.decomposition P.assignment state.requests p)
  collect := fun _ state delivered => {state with partials := delivered}

/-- Original holders send sparse columns and rows to their middle-index nodes. -/
def gatherStage : LocalPipeline.Stage (Fin n) (State P S) S where
  Packet := HelperPlan.Input A B
  packetFinite := inferInstance
  packetDecEq := inferInstance
  source := original
  destination := InputGather.middle
  rounds := 2 * (K * d + 2 * d)
  plan := P.gather
  prepare := fun _ state e => state.originalInputs e
  collect := fun _ state delivered => {state with middleInputs := delivered}

/-- Middle-index nodes compute products from gathered inputs and deliver them. -/
def residualStage : LocalPipeline.Stage (Fin n) (State P S) S where
  Packet := ResidualPacket P
  packetFinite := inferInstance
  packetDecEq := inferInstance
  source := ResidualDelivery.source A B Q P.decomposition.residual
  destination := ResidualDelivery.destination A B Q P.decomposition.residual P.out
  rounds := 2 * (threshold d + d)
  plan := P.residual
  prepare := fun _ state p => some
    (Computation.computeResidual P.decomposition.residual state.middleInputs p)
  collect := fun _ state delivered => {state with products := delivered}

theorem cluster_exists (q : {q // q ∈ Q}) (hr : q.val ∉ P.decomposition.residual) :
    ∃ c : Fin P.decomposition.clusters.length, q.val ∈ P.decomposition.clusters[c] := by
  rcases (P.decomposition.cover q.val).mp q.property with hres | ⟨C, hC, hqC⟩
  · exact (hr hres).elim
  · obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hC
    refine ⟨⟨i, hi⟩, ?_⟩
    change q.val ∈ P.decomposition.clusters[i]
    rw [heq]
    exact hqC

/-- The cluster selected for an output is determined by public code alone. -/
def clusterFor (q : {q // q ∈ Q}) (hr : q.val ∉ P.decomposition.residual) :
    {c : Fin P.decomposition.clusters.length // q.val ∈ P.decomposition.clusters[c]} :=
  ⟨Classical.choose (cluster_exists P q hr), Classical.choose_spec (cluster_exists P q hr)⟩

/-- An output holder adds its own delivered packets. -/
def finish (_node : Fin n) (state : State P S) (q : {q // q ∈ Q}) : S :=
  if hr : q.val ∈ P.decomposition.residual then
    Computation.computeResidualOutput P.decomposition.residual state.products q hr
  else
    let c := clusterFor P q hr
    Computation.computeClusteredOutput P.decomposition state.partials q c.val c.property

/-- The actual distributed program; no numerical matrices occur in its code. -/
def program : LocalPipeline.Program (Fin n) (View A B S) (State P S) S ({q // q ∈ Q} → S) where
  init := initState P
  stages := [firstStage P, secondStage P, partialStage P, gatherStage P, residualStage P]
  finish := finish P

theorem program_rounds : (program (S := S) P).rounds = P.rounds := by
  simp [LocalPipeline.Program.rounds, program, firstStage, secondStage, partialStage,
    gatherStage, residualStage, Plan.rounds, Nat.add_assoc]

/-- The mathematical input instance supplies each numerical entry only to its
actual public original holder. -/
def views (original : HelperPlan.Input A B → Fin n) (U V : Matrix (Fin n) (Fin n) S) (node : Fin n) : View A B S :=
  fun e => if original e = node then some (Computation.inputValue U V e) else none

def initialConfiguration (localViews : Fin n → View A B S) : Fin n → State P S :=
  fun node => initState P node (localViews node)

def afterFirst (localViews : Fin n → View A B S) : Fin n → State P S :=
  (firstStage P).run (initialConfiguration P localViews)

def afterSecond (localViews : Fin n → View A B S) : Fin n → State P S :=
  (secondStage P).run (afterFirst P localViews)

def afterPartial (localViews : Fin n → View A B S) : Fin n → State P S :=
  (partialStage P).run (afterSecond P localViews)

def afterGather (localViews : Fin n → View A B S) : Fin n → State P S :=
  (gatherStage P).run (afterPartial P localViews)

def afterResidual (localViews : Fin n → View A B S) : Fin n → State P S :=
  (residualStage P).run (afterGather P localViews)

theorem execution_eq_afterResidual (localViews : Fin n → View A B S) :
    (program P).execute localViews = afterResidual P localViews := rfl

omit [Semiring S] in
theorem first_available (U V : Matrix (Fin n) (Fin n) S) (e : Needed P) :
    (afterFirst P (views original U V) (P.broadcaster e.val)).broadcastInputs e =
      some (Computation.inputValue U V e.val) := by
  change Model.executeFrom P.first _
    (fun node e => (views original U V node) e.val) (P.broadcaster e.val) e = _
  apply Model.executeFrom_delivers P.first _ (fun e => Computation.inputValue U V e.val)
  intro e
  simp [views]

omit [Semiring S] in
theorem second_available (U V : Matrix (Fin n) (Fin n) S) (r : Request P) :
    (afterSecond P (views original U V) (P.place (HelperPlan.Request.helper P.assignment r))).requests r =
      some (Computation.inputValue U V r.input) := by
  change Model.executeFrom P.second _
    (fun node r => (afterFirst P (views original U V) node).broadcastInputs
      ⟨r.input, Multicast.request_needed _ r⟩)
    (P.place (HelperPlan.Request.helper P.assignment r)) r = _
  apply Model.executeFrom_delivers P.second _ (fun r => Computation.inputValue U V r.input)
  intro r
  exact first_available P U V ⟨r.input, Multicast.request_needed _ r⟩

theorem partial_available (U V : Matrix (Fin n) (Fin n) S) (p : PartialPacket P) :
    (afterPartial P (views original U V) (P.out p.1)).partials p =
      some (Computation.clusteredPartialValue (A := A) (B := B)
        P.decomposition U V P.assignment p) := by
  change Model.executeFrom P.«partial» _
    (fun node p => some (Computation.computePartial P.decomposition P.assignment
      (afterSecond P (views original U V) node).requests p)) (P.out p.1) p = _
  apply Model.executeFrom_delivers P.«partial» _
    (Computation.clusteredPartialValue (A := A) (B := B) P.decomposition U V P.assignment)
  intro p
  apply congrArg some
  apply Computation.computePartial_eq_value
  intro r hr
  simpa only [hr, Function.comp_apply, PartialDelivery.helper] using second_available P U V r

theorem gather_available (U V : Matrix (Fin n) (Fin n) S) (e : HelperPlan.Input A B) :
    (afterGather P (views original U V) (Computation.inputMiddle e)).middleInputs e =
      some (Computation.inputValue U V e) := by
  change Model.executeFrom P.gather _ (fun node e => views original U V node e)
    (Computation.inputMiddle e) e = _
  apply Model.executeFrom_delivers P.gather _ (Computation.inputValue U V)
  intro e
  simp [views]

theorem residual_available (U V : Matrix (Fin n) (Fin n) S) (p : ResidualPacket P) :
    (afterResidual P (views original U V) (P.out p.1)).products p =
      some (Computation.residualValue P.decomposition.residual U V p) := by
  change Model.executeFrom P.residual _
    (fun node p => some (Computation.computeResidual P.decomposition.residual
      (afterGather P (views original U V) node).middleInputs p)) (P.out p.1) p = _
  apply Model.executeFrom_delivers P.residual _
    (Computation.residualValue P.decomposition.residual U V)
  intro p
  apply congrArg some
  apply Computation.computeResidual_eq_value
  intro e he
  simpa only [he, ResidualDelivery.source] using gather_available P U V e

/-- Every assigned output of the locally executed five-phase program is the
requested matrix-product entry, for arbitrary supported semiring values. -/
theorem output_correct (U V : Matrix (Fin n) (Fin n) S)
    (hU : Algebra.SupportedBy U A) (hV : Algebra.SupportedBy V B)
    (q : {q // q ∈ Q}) :
    (program P).output (views original U V) (P.out q) q = (U * V) q.val.1 q.val.2 := by
  change finish P (P.out q) (afterResidual P (views original U V) (P.out q)) q = _
  unfold finish
  split_ifs with hr
  · exact Computation.computeResidualOutput_eq_mul P.decomposition.residual U V hU hV
      (afterResidual P (views original U V) (P.out q)).products q hr
      (fun j => residual_available P U V
        (Computation.residualPacket P.decomposition.residual q hr j))
  · exact Computation.computeClusteredOutput_eq_mul P.decomposition U V hU hV P.assignment
      (afterResidual P (views original U V) (P.out q)).partials q
      (clusterFor P q hr).val (clusterFor P q hr).property
      (fun member => partial_available P U V
        (Computation.partialPacket P.decomposition q
          (clusterFor P q hr).val (clusterFor P q hr).property member))

end

end SparseMM.SupportedProgram
