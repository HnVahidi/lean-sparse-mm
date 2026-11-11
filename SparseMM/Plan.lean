module

public import SparseMM.HelperPlan
public import SparseMM.Multicast
public import SparseMM.OutputPlan
public import SparseMM.PartialDelivery
public import SparseMM.Model
public import SparseMM.InputGather

@[expose] public section

/-!
# Public plan for the supported sparse multiplication algorithm

All choices in this package precede the numerical entries. The constructor
chooses a decomposition, helper assignments and placements, one common output
assignment, broadcasters, and every communication schedule from the public
masks and original input holders alone.
-/

namespace SparseMM

/-- Complete public code for the finite supported algorithm. No numerical
matrix or assumed algorithm-correctness field occurs in this data. -/
structure Plan {n d K : ℕ} (A B Q : Mask n)
    (original : HelperPlan.Input A B → Fin n) where
  decomposition : Clustering Q d (threshold d)
  assignment : Fin decomposition.clusters.length → Fin n → Fin (teamSize d)
  assignment_load : ∀ c b,
    Balancing.binLoad (clusterInputCost A B decomposition.clusters[c]) (assignment c) b ≤
      4 * threshold d
  place : HelperPlan.Helper decomposition (teamSize d) ↪ Fin n
  out : {p // p ∈ Q} → Fin n
  output_count : ∀ node, Counting.count out node ≤ d
  output_weight : ∀ node,
    Counting.load out (fun q => residualWeight A B decomposition.residual q.val) node ≤
      threshold d + d
  broadcaster : HelperPlan.Input A B → Fin n
  first : Model.StaticPlan
    (fun e : Multicast.Needed (HelperPlan.Request.input (A := A) (B := B) (D := decomposition)) =>
      original e.val)
    (fun e => broadcaster e.val) (2 * max (K * d) (4 * threshold d + d))
  second : Model.StaticPlan
    (broadcaster ∘ HelperPlan.Request.input (A := A) (B := B) (D := decomposition))
    (place ∘ HelperPlan.Request.helper assignment) (2 * (4 * threshold d + d))
  «partial» : Model.StaticPlan
    (place ∘ PartialDelivery.helper (h := teamSize d) decomposition)
    (PartialDelivery.destination decomposition out)
    (2 * (threshold d + d * teamSize d))
  gather : Model.StaticPlan original (InputGather.middle (A := A) (B := B))
    (2 * (K * d + 2 * d))
  residual : Model.StaticPlan
    (ResidualDelivery.source A B Q decomposition.residual)
    (ResidualDelivery.destination A B Q decomposition.residual out)
    (2 * (threshold d + d))

namespace Plan

/-- Sum of the five actual phase lengths. This expression contains no
numerical input values. -/
def rounds {n d K : ℕ} {A B Q : Mask n} {original : HelperPlan.Input A B → Fin n}
    (_plan : Plan (d := d) (K := K) A B Q original) : ℕ :=
  2 * max (K * d) (4 * threshold d + d) +
  2 * (4 * threshold d + d) +
  2 * (threshold d + d * teamSize d) +
  2 * (K * d + 2 * d) +
  2 * (threshold d + d)

/-- A fixed explicit round constant for the entire public plan. -/
theorem rounds_le {n d K : ℕ} {A B Q : Mask n}
    {original : HelperPlan.Input A B → Fin n}
    (plan : Plan (d := d) (K := K) A B Q original) :
    plan.rounds ≤ (4 * K + 32) * threshold d := by
  have hdt := degree_le_threshold d
  have hK := Nat.mul_le_mul_left K hdt
  have hm : max (K * d) (4 * threshold d + d) ≤ K * d + (4 * threshold d + d) :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have ht : d * teamSize d = threshold d := rfl
  unfold rounds
  rw [ht]
  nlinarith

end Plan

/-- The entire public scheduling plan exists from the stated masks and a
bounded public initial input distribution. In particular, no schedule or
balanced output assignment is an unproved hypothesis. -/
theorem exists_public_plan {n d K : ℕ} (hn : 0 < n) (hd : 0 < d)
    (A B Q : Mask n) (hA : UniformSparse A d) (hB : UniformSparse B d)
    (hQ : UniformSparse Q d) (original : HelperPlan.Input A B → Fin n)
    (horiginal : ∀ node, Counting.count original node ≤ K * d) :
    Nonempty (Plan (d := d) (K := K) A B Q original) := by
  classical
  obtain ⟨D⟩ := exists_clustering Q d (threshold d) (threshold_pos hd)
  obtain ⟨assignment, hassignment⟩ := HelperPlan.exists_helper_assignment D hA hB
  obtain ⟨place⟩ := HelperPlan.exists_helper_placement D hd hQ
  obtain ⟨out, hcount, hweight⟩ := exists_output_plan hn A B Q D.residual
    hA hB hQ D.residual_sub D.sparse
  obtain ⟨broadcaster, ⟨first, hfirst⟩, ⟨second, hsecond⟩⟩ :=
    Multicast.exists_two_stage_schedules n (K * d) (4 * threshold d) d hn
      (HelperPlan.Request.input (A := A) (B := B) (D := D))
      (place ∘ HelperPlan.Request.helper assignment) original
      (HelperPlan.input_request_count_le D hQ)
      (HelperPlan.physical_helper_count_le D assignment hassignment place)
      horiginal
  obtain ⟨partialSlot, hpartial⟩ := PartialDelivery.exists_schedule (h := teamSize d)
    D place place.injective out hcount
  obtain ⟨residual, hresidual⟩ := ResidualDelivery.exists_schedule A B Q D.residual
    hA hB D.sparse out hweight
  obtain ⟨gather, hgather⟩ := InputGather.exists_schedule A B hA hB K original horiginal
  exact ⟨{
    decomposition := D
    assignment := assignment
    assignment_load := hassignment
    place := place
    out := out
    output_count := hcount
    output_weight := hweight
    broadcaster := broadcaster
    first := ⟨first, hfirst⟩
    second := ⟨second, hsecond⟩
    «partial» := ⟨partialSlot, hpartial⟩
    gather := ⟨gather, hgather⟩
    residual := ⟨residual, hresidual⟩ }⟩

end SparseMM
