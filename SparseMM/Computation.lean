module

public import SparseMM.Algebra
public import SparseMM.HelperPlan
public import SparseMM.PartialDelivery
public import SparseMM.ResidualDelivery
public import SparseMM.Model

/-!
# Local arithmetic between the communication phases

The functions `computePartial` and `computeResidual` read only an explicitly
supplied local optional-value memory. Their correctness lemmas require actual
availability of their input records at that node. Global matrices describe
the specification, and are not arguments to these local computation functions.
-/

@[expose] public section

namespace SparseMM.Computation

open scoped BigOperators

variable {n d t h : ℕ} {A B Q : Mask n} {S : Type*} [Semiring S]

/-- The mathematical value carried by one allowed input record. -/
def inputValue (U V : Matrix (Fin n) (Fin n) S) (e : HelperPlan.Input A B) : S :=
  match e with
  | Sum.inl a => U a.val.1 a.val.2
  | Sum.inr b => V b.val.1 b.val.2

/-- Input-to-middle gathering sends a left input to its column index and a
right input to its row index. This destination is entirely public. -/
def inputMiddle (e : HelperPlan.Input A B) : Fin n :=
  match e with
  | Sum.inl a => a.val.2
  | Sum.inr b => b.val.1

variable (D : Clustering Q d t)

/-- Potential middle indices assigned to the helper producing this packet. -/
abbrev AssignedMiddle
    (assignment : Fin D.clusters.length → Fin n → Fin h)
    (p : PartialDelivery.Packet (h := h) D) :=
  {j : Fin n // j ∈ middleSet A B p.1.val ∧
    assignment p.2.val.1 j = p.2.val.2}

/-- The exact request record carrying this partial sum's needed left input. -/
def requestA (p : PartialDelivery.Packet (h := h) D) (j : Fin n)
    (hj : j ∈ middleSet A B p.1.val) : HelperPlan.Request A B D :=
  ⟨p.2.val.1, j, Sum.inl ⟨p.1.val.1, by
    apply Finset.mem_inter.mpr
    constructor
    · have ha := (Finset.mem_filter.mp hj).2.1
      simpa [colMask] using ha
    · exact Finset.mem_image.mpr ⟨p.1.val, p.2.property, rfl⟩⟩⟩

/-- The exact request record carrying this partial sum's needed right input. -/
def requestB (p : PartialDelivery.Packet (h := h) D) (j : Fin n)
    (hj : j ∈ middleSet A B p.1.val) : HelperPlan.Request A B D :=
  ⟨p.2.val.1, j, Sum.inr ⟨p.1.val.2, by
    apply Finset.mem_inter.mpr
    constructor
    · have hb := (Finset.mem_filter.mp hj).2.2
      simpa [rowMask] using hb
    · exact Finset.mem_image.mpr ⟨p.1.val, p.2.property, rfl⟩⟩⟩

theorem requestA_helper (assignment : Fin D.clusters.length → Fin n → Fin h)
    (p : PartialDelivery.Packet (h := h) D) (j : AssignedMiddle (A := A) (B := B) D assignment p) :
    HelperPlan.Request.helper assignment (requestA D p j.val j.property.1) = p.2.val := by
  exact Prod.ext rfl j.property.2

theorem requestB_helper (assignment : Fin D.clusters.length → Fin n → Fin h)
    (p : PartialDelivery.Packet (h := h) D) (j : AssignedMiddle (A := A) (B := B) D assignment p) :
    HelperPlan.Request.helper assignment (requestB D p j.val j.property.1) = p.2.val := by
  exact Prod.ext rfl j.property.2

/-- Mathematical specification of one clustered partial-sum packet. -/
def clusteredPartialValue (U V : Matrix (Fin n) (Fin n) S)
    (assignment : Fin D.clusters.length → Fin n → Fin h)
    (p : PartialDelivery.Packet (h := h) D) : S :=
  ∑ j : AssignedMiddle (A := A) (B := B) D assignment p, U p.1.val.1 j.val * V j.val p.1.val.2

/-- The helper computes using only its received request records. An absent
record defaults to zero; the correctness premise below rules out absence for
every requested record that is actually used. -/
def computePartial (assignment : Fin D.clusters.length → Fin n → Fin h)
    (memory : Model.LocalState (HelperPlan.Request A B D) S)
    (p : PartialDelivery.Packet (h := h) D) : S :=
  ∑ j : AssignedMiddle (A := A) (B := B) D assignment p,
    (memory (requestA D p j.val j.property.1)).getD 0 *
      (memory (requestB D p j.val j.property.1)).getD 0

/-- Complete input-request availability at this helper is sufficient to compute
its true partial value. The local code itself has no access to `U` or `V`. -/
theorem computePartial_eq_value (U V : Matrix (Fin n) (Fin n) S)
    (assignment : Fin D.clusters.length → Fin n → Fin h)
    (memory : Model.LocalState (HelperPlan.Request A B D) S)
    (p : PartialDelivery.Packet (h := h) D)
    (havailable : ∀ r : HelperPlan.Request A B D,
      HelperPlan.Request.helper assignment r = p.2.val →
      memory r = some (inputValue U V r.input)) :
    computePartial D assignment memory p = clusteredPartialValue (A := A) (B := B) D U V assignment p := by
  apply Finset.sum_congr rfl
  intro j _
  rw [havailable _ (requestA_helper D assignment p j),
    havailable _ (requestB_helper D assignment p j)]
  rfl

/-- Only request records destined to this helper can affect its computation. -/
theorem computePartial_locality (assignment : Fin D.clusters.length → Fin n → Fin h)
    (memory memory' : Model.LocalState (HelperPlan.Request A B D) S)
    (p : PartialDelivery.Packet (h := h) D)
    (heq : ∀ r : HelperPlan.Request A B D,
      HelperPlan.Request.helper assignment r = p.2.val → memory r = memory' r) :
    computePartial D assignment memory p = computePartial D assignment memory' p := by
  apply Finset.sum_congr rfl
  intro j _
  rw [heq _ (requestA_helper D assignment p j), heq _ (requestB_helper D assignment p j)]

/-- Conversion to the finite filtered sum used by the arithmetic identities. -/
theorem clusteredPartialValue_eq_maskedPartialSum (U V : Matrix (Fin n) (Fin n) S)
    (assignment : Fin D.clusters.length → Fin n → Fin h)
    (p : PartialDelivery.Packet (h := h) D) :
    clusteredPartialValue (A := A) (B := B) D U V assignment p =
      Algebra.maskedPartialSum U V A B (assignment p.2.val.1)
        p.2.val.2 p.1.val.1 p.1.val.2 := by
  unfold clusteredPartialValue Algebra.maskedPartialSum
  exact (Finset.sum_subtype
    (p := fun j : Fin n => j ∈ middleSet A B p.1.val ∧
      assignment p.2.val.1 j = p.2.val.2)
    ((middleSet A B p.1.val).filter fun j => assignment p.2.val.1 j = p.2.val.2)
    (fun _ => Finset.mem_filter) (fun j => U p.1.val.1 j * V j p.1.val.2)).symm

/-- For a fixed clustered output, there is one partial-sum packet per member
of its assigned cluster's team. -/
def partialPacket (q : {q // q ∈ Q}) (c : Fin D.clusters.length)
    (hqc : q.val ∈ D.clusters[c]) (member : Fin h) : PartialDelivery.Packet (h := h) D :=
  ⟨q, ⟨(c, member), hqc⟩⟩

/-- Adding the true team packets yields the requested matrix product entry. -/
theorem clustered_values_sum (U V : Matrix (Fin n) (Fin n) S)
    (hU : Algebra.SupportedBy U A) (hV : Algebra.SupportedBy V B)
    (assignment : Fin D.clusters.length → Fin n → Fin h)
    (q : {q // q ∈ Q}) (c : Fin D.clusters.length) (hqc : q.val ∈ D.clusters[c]) :
    (∑ member : Fin h, clusteredPartialValue (A := A) (B := B) D U V assignment
      (partialPacket D q c hqc member)) = (U * V) q.val.1 q.val.2 := by
  simp_rw [clusteredPartialValue_eq_maskedPartialSum]
  exact Algebra.maskedPartialSums_eq_mul U V A B hU hV (assignment c) q.val.1 q.val.2

/-- The output holder adds its locally received partial-sum packets. -/
def computeClusteredOutput
    (memory : Model.LocalState (PartialDelivery.Packet (h := h) D) S)
    (q : {q // q ∈ Q}) (c : Fin D.clusters.length) (hqc : q.val ∈ D.clusters[c]) : S :=
  ∑ member : Fin h, (memory (partialPacket D q c hqc member)).getD 0

theorem computeClusteredOutput_eq_mul (U V : Matrix (Fin n) (Fin n) S)
    (hU : Algebra.SupportedBy U A) (hV : Algebra.SupportedBy V B)
    (assignment : Fin D.clusters.length → Fin n → Fin h)
    (memory : Model.LocalState (PartialDelivery.Packet (h := h) D) S)
    (q : {q // q ∈ Q}) (c : Fin D.clusters.length) (hqc : q.val ∈ D.clusters[c])
    (havailable : ∀ member : Fin h, memory (partialPacket D q c hqc member) =
      some (clusteredPartialValue (A := A) (B := B) D U V assignment (partialPacket D q c hqc member))) :
    computeClusteredOutput D memory q c hqc = (U * V) q.val.1 q.val.2 := by
  unfold computeClusteredOutput
  simp_rw [havailable, Option.getD_some]
  exact clustered_values_sum D U V hU hV assignment q c hqc

variable (R : Mask n)

/-- The left input label used by a residual product. -/
def residualInputA (p : ResidualDelivery.Packet A B Q R) : HelperPlan.Input A B :=
  Sum.inl ⟨(p.1.val.1, p.2.val), by
    exact (Finset.mem_filter.mp p.2.property.2).2.1⟩

/-- The right input label used by a residual product. -/
def residualInputB (p : ResidualDelivery.Packet A B Q R) : HelperPlan.Input A B :=
  Sum.inr ⟨(p.2.val, p.1.val.2), by
    exact (Finset.mem_filter.mp p.2.property.2).2.2⟩

/-- Mathematical value of a residual product packet. -/
def residualValue (U V : Matrix (Fin n) (Fin n) S)
    (p : ResidualDelivery.Packet A B Q R) : S := U p.1.val.1 p.2.val * V p.2.val p.1.val.2

/-- A middle-index machine computes a residual product entirely from its
locally gathered left and right input records. -/
def computeResidual (memory : Model.LocalState (HelperPlan.Input A B) S)
    (p : ResidualDelivery.Packet A B Q R) : S :=
  (memory (residualInputA R p)).getD 0 * (memory (residualInputB R p)).getD 0

theorem computeResidual_eq_value (U V : Matrix (Fin n) (Fin n) S)
    (memory : Model.LocalState (HelperPlan.Input A B) S)
    (p : ResidualDelivery.Packet A B Q R)
    (havailable : ∀ e : HelperPlan.Input A B, inputMiddle e = p.2.val →
      memory e = some (inputValue U V e)) :
    computeResidual R memory p = residualValue R U V p := by
  unfold computeResidual
  rw [havailable _ rfl, havailable _ rfl]
  rfl

theorem computeResidual_locality
    (memory memory' : Model.LocalState (HelperPlan.Input A B) S)
    (p : ResidualDelivery.Packet A B Q R)
    (heq : ∀ e : HelperPlan.Input A B, inputMiddle e = p.2.val → memory e = memory' e) :
    computeResidual R memory p = computeResidual R memory' p := by
  unfold computeResidual
  rw [heq _ rfl, heq _ rfl]

/-- The product packet for one potential middle index of a residual output. -/
def residualPacket (q : {q // q ∈ Q}) (hr : q.val ∈ R)
    (j : {j // j ∈ middleSet A B q.val}) : ResidualDelivery.Packet A B Q R :=
  ⟨q, ⟨j.val, hr, j.property⟩⟩

/-- All true residual packets sum to the matrix entry, including when the
middle-index subtype is empty and the output is zero. -/
theorem residual_values_sum (U V : Matrix (Fin n) (Fin n) S)
    (hU : Algebra.SupportedBy U A) (hV : Algebra.SupportedBy V B)
    (q : {q // q ∈ Q}) (hr : q.val ∈ R) :
    (∑ j : {j // j ∈ middleSet A B q.val},
      residualValue R U V (residualPacket R q hr j)) = (U * V) q.val.1 q.val.2 := by
  have hsum : (∑ j : {j // j ∈ middleSet A B q.val},
      residualValue R U V (residualPacket R q hr j)) =
      Algebra.maskedEntry U V A B q.val.1 q.val.2 := by
    unfold Algebra.maskedEntry
    exact (Finset.sum_subtype (p := fun j : Fin n => j ∈ middleSet A B q.val)
      (middleSet A B q.val) (fun _ => Iff.rfl)
      (fun j => U q.val.1 j * V j q.val.2)).symm
  rw [hsum]
  exact Algebra.maskedEntry_eq_mul U V A B hU hV q.val.1 q.val.2

/-- A residual output holder adds only its locally received product packets. -/
def computeResidualOutput
    (memory : Model.LocalState (ResidualDelivery.Packet A B Q R) S)
    (q : {q // q ∈ Q}) (hr : q.val ∈ R) : S :=
  ∑ j : {j // j ∈ middleSet A B q.val}, (memory (residualPacket R q hr j)).getD 0

theorem computeResidualOutput_eq_mul (U V : Matrix (Fin n) (Fin n) S)
    (hU : Algebra.SupportedBy U A) (hV : Algebra.SupportedBy V B)
    (memory : Model.LocalState (ResidualDelivery.Packet A B Q R) S)
    (q : {q // q ∈ Q}) (hr : q.val ∈ R)
    (havailable : ∀ j : {j // j ∈ middleSet A B q.val},
      memory (residualPacket R q hr j) = some (residualValue R U V (residualPacket R q hr j))) :
    computeResidualOutput R memory q hr = (U * V) q.val.1 q.val.2 := by
  unfold computeResidualOutput
  simp_rw [havailable, Option.getD_some]
  exact residual_values_sum R U V hU hV q hr

end SparseMM.Computation
