module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Nat

@[expose] public section

/-!
# Balancing fixed output profiles by relabeling processors

For every finite profile of current loads and every finite profile of output
weights, a permutation pairs the two profiles in opposite orders. The proof
minimizes their scalar product and rules out an improving transposition. Repeated
pairing preserves the spread of the loads and conserves their exact sum.

The permutations depend only on the profiles, so a fixed sequence of public
output profiles gives fixed permutations. These are combinatorial statements;
transport of inputs and simulation of a relabeled protocol are separate results.
-/

open scoped BigOperators

namespace SparseMM
namespace LoadBalancing

/-- Pairwise spread at most `W`, expressed without natural subtraction. -/
def HasSpread {ι : Type*} (f : ι → ℕ) (W : ℕ) : Prop :=
  ∀ i j, f i ≤ f j + W

/-- Opposed additions preserve a common spread bound. Equal loads may receive
different increments, so the ordering premise uses a strict inequality. -/
theorem sum_spread_of_opposed {ι : Type*}
    (f g : ι → ℕ) (W : ℕ)
    (hfspread : HasSpread f W) (hgspread : HasSpread g W)
    (hopposed : ∀ i j, f i < f j → g j ≤ g i) :
    HasSpread (fun i => f i + g i) W := by
  intro i j
  by_cases hij : f i ≤ f j
  · calc
      f i + g i ≤ f j + (g j + W) := Nat.add_le_add hij (hgspread i j)
      _ = (f j + g j) + W := (Nat.add_assoc _ _ _).symm
  · calc
      f i + g i ≤ (f j + W) + g j :=
        Nat.add_le_add (hfspread i j) (hopposed j i (Nat.lt_of_not_ge hij))
      _ = (f j + g j) + W := Nat.add_right_comm _ _ _

/-- A permutation pairs arbitrary finite profiles in opposite orders. The
permutation maps virtual processors to physical processors, hence its inverse
appears in the physical processor's assigned weight. -/
theorem exists_opposed_permutation {ι : Type*} [Fintype ι]
    (f w : ι → ℕ) :
    ∃ p : Equiv.Perm ι, ∀ i j, f i < f j → w (p.symm j) ≤ w (p.symm i) := by
  classical
  obtain ⟨q, _hq, hmin⟩ := Finset.univ.exists_min_image
    (fun q : Equiv.Perm ι => ∑ i : ι, f i * w (q i)) Finset.univ_nonempty
  refine ⟨q.symm, ?_⟩
  intro i j hij
  change w (q j) ≤ w (q i)
  by_contra hn
  have hw : w (q i) < w (q j) := Nat.lt_of_not_ge hn
  have hne : i ≠ j := by
    intro h
    subst j
    exact (Nat.lt_irrefl _) hij
  let q' : Equiv.Perm ι := (Equiv.swap i j).trans q
  have hminimum := hmin q' (Finset.mem_univ _)
  have hdecrease : (∑ k : ι, f k * w (q' k)) < ∑ k : ι, f k * w (q k) := by
    simp only [q', ← Finset.univ.sum_erase_add _ (Finset.mem_univ i),
      ← (Finset.univ.erase i).sum_erase_add _
        (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ j⟩),
      Nat.add_assoc, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
    refine add_lt_add_of_le_of_lt (Finset.sum_congr rfl fun k hk => ?_).le ?_
    · simp only [Finset.mem_erase] at hk
      rw [Equiv.swap_apply_of_ne_of_ne hk.2.1 hk.1]
    · simpa only [Nat.add_comm] using mul_add_mul_lt_mul_add_mul hij hw
  exact (Nat.not_lt_of_ge hminimum) hdecrease

/-- Each bounded output profile has a permutation that both opposes the current
loads and preserves their spread. No ordering premise is assumed. -/
theorem exists_balancing_permutation {ι : Type*} [Fintype ι]
    (f w : ι → ℕ) (W : ℕ) (hf : HasSpread f W) (hw : ∀ i, w i ≤ W) :
    ∃ p : Equiv.Perm ι,
      (∀ i j, f i < f j → w (p.symm j) ≤ w (p.symm i)) ∧
      HasSpread (fun i => f i + w (p.symm i)) W := by
  obtain ⟨p, hp⟩ := exists_opposed_permutation f w
  refine ⟨p, hp, sum_spread_of_opposed f (fun i => w (p.symm i)) W hf ?_ hp⟩
  intro i j
  exact (hw (p.symm i)).trans (Nat.le_add_left W (w (p.symm j)))

/-- The accumulated output load at a physical processor. Each permutation maps
virtual processor names in one invocation to physical processor names. -/
def assignedLoad {ι τ : Type*} [Fintype τ]
    (weights : τ → ι → ℕ) (permutations : τ → Equiv.Perm ι) (i : ι) : ℕ :=
  ∑ t : τ, weights t ((permutations t).symm i)

/-- Relabeling processors conserves the exact number of outputs, for every
choice of permutations. -/
theorem assignedLoad_sum {ι τ : Type*} [Fintype ι] [Fintype τ]
    (weights : τ → ι → ℕ) (permutations : τ → Equiv.Perm ι) :
    (∑ i : ι, assignedLoad weights permutations i) = ∑ t : τ, ∑ i : ι, weights t i := by
  classical
  unfold assignedLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _ht
  exact (permutations t).symm.sum_comp (weights t)

/-- A spread bound yields a maximum-load bound after clearing the averaging
denominator. The statement also covers an empty processor type. -/
theorem scaled_load_le_total_add_slack {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (W : ℕ) (hf : HasSpread f W) (i : ι) :
    Fintype.card ι * f i ≤ (∑ j : ι, f j) + Fintype.card ι * W := by
  classical
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _hj => hf i j)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id, Finset.sum_add_distrib] using h

/-- Every finite sequence of bounded profiles admits relabelings that keep the
final accumulated load spread at most the bound on a single profile entry. The
inductive construction adds each profile opposite to the preceding loads. -/
theorem exists_permutations_spread {ι : Type*} [Fintype ι]
    (T W : ℕ) (weights : Fin T → ι → ℕ) (hweights : ∀ t i, weights t i ≤ W) :
    ∃ permutations : Fin T → Equiv.Perm ι,
      HasSpread (assignedLoad weights permutations) W := by
  classical
  induction T with
  | zero =>
      refine ⟨fun t => Fin.elim0 t, ?_⟩
      intro i j
      simp [assignedLoad]
  | succ T ih =>
      obtain ⟨prior, hprior⟩ := ih (fun t => weights t.castSucc)
        (fun t i => hweights t.castSucc i)
      obtain ⟨p, _hopposed, hbalance⟩ := exists_balancing_permutation
        (assignedLoad (fun t => weights t.castSucc) prior) (weights (Fin.last T))
        W hprior (hweights (Fin.last T))
      refine ⟨Fin.snoc prior p, ?_⟩
      intro i j
      simpa only [assignedLoad, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
        using hbalance i j

/-- Complete finite balancing statement: actual permutations, a bounded load
spread, exact conservation of all output weights, and a maximum-load bound.
`n > 0` is unnecessary for this denominator-cleared formulation. -/
theorem exists_balanced_permutations (n T W : ℕ)
    (weights : Fin T → Fin n → ℕ) (hweights : ∀ t i, weights t i ≤ W) :
    ∃ permutations : Fin T → Equiv.Perm (Fin n),
      HasSpread (assignedLoad weights permutations) W ∧
      (∑ i : Fin n, assignedLoad weights permutations i) =
        (∑ t : Fin T, ∑ i : Fin n, weights t i) ∧
      ∀ i : Fin n, n * assignedLoad weights permutations i ≤
        (∑ t : Fin T, ∑ j : Fin n, weights t j) + n * W := by
  obtain ⟨permutations, hspread⟩ := exists_permutations_spread T W weights hweights
  have hsum := assignedLoad_sum weights permutations
  refine ⟨permutations, hspread, hsum, ?_⟩
  intro i
  simpa only [Fintype.card_fin, hsum] using
    scaled_load_le_total_add_slack (assignedLoad weights permutations) W hspread i

end LoadBalancing
end SparseMM
