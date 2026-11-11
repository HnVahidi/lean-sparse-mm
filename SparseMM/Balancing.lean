module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Max
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Greedy assignment of weighted items to helper machines

This is the finite combinatorial content of the paper's greedy-assignment
lemma. Items are assigned individually. A new item is sent to a bin of minimum
current load; the maximum item weight bounds the final load spread. No
communication protocol or asymptotic round bound is postulated here.
-/

open scoped BigOperators

namespace SparseMM.Balancing

/-- Total weight of the items whose assigned helper is `b`. -/
def binLoad {T n : ℕ} (weights : Fin T → ℕ)
    (assignment : Fin T → Fin n) (b : Fin n) : ℕ :=
  ∑ t : Fin T, if assignment t = b then weights t else 0

/-- Every pair of loads differs by at most `W`, without truncated subtraction. -/
def HasSpread {ι : Type*} (load : ι → ℕ) (W : ℕ) : Prop :=
  ∀ i j, load i ≤ load j + W

/-- Adding a bounded item to a least-loaded bin preserves the spread bound. -/
theorem add_to_min_preserves_spread {ι : Type*} [DecidableEq ι]
    (load : ι → ℕ) (W w : ℕ) (b : ι)
    (hs : HasSpread load W) (hw : w ≤ W)
    (hmin : ∀ j, load b ≤ load j) :
    HasSpread (fun i => load i + if i = b then w else 0) W := by
  intro i j
  by_cases hi : i = b
  · subst i
    by_cases hj : j = b
    · subst j
      simp
    · simp only [ite_true, ite_eq_right hj, Nat.add_zero]
      exact Nat.add_le_add (hmin j) hw
  · by_cases hj : j = b
    · subst j
      simp only [ite_eq_right hi, ite_true, Nat.add_zero]
      have h := hs i b
      omega
    · simpa only [ite_eq_right hi, ite_eq_right hj, Nat.add_zero] using hs i j

/-- Splitting the last item expresses its contribution to each actual bin. -/
theorem binLoad_snoc {T n : ℕ} (weights : Fin (T + 1) → ℕ)
    (assignment : Fin T → Fin n) (b i : Fin n) :
    binLoad weights (Fin.snoc assignment b) i =
      binLoad (fun t => weights t.castSucc) assignment i +
        if i = b then weights (Fin.last T) else 0 := by
  classical
  simp only [binLoad, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  by_cases h : i = b
  · simp [h]
  · simp [h, Ne.symm h]

/-- A bounded weighted item family admits an actual assignment with bounded
load spread. The proof constructs it by repeatedly choosing a minimum load. -/
theorem exists_assignment_spread (n T W : ℕ) (hn : 0 < n)
    (weights : Fin T → ℕ) (hw : ∀ t, weights t ≤ W) :
    ∃ assignment : Fin T → Fin n, HasSpread (binLoad weights assignment) W := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  induction T with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      intro i j
      simp [binLoad]
  | succ T ih =>
      obtain ⟨prior, hprior⟩ := ih (fun t => weights t.castSucc) (fun t => hw t.castSucc)
      let load := binLoad (fun t => weights t.castSucc) prior
      obtain ⟨b, _hb, hmin⟩ := (Finset.univ : Finset (Fin n)).exists_min_image
        load Finset.univ_nonempty
      refine ⟨Fin.snoc prior b, ?_⟩
      intro i j
      rw [binLoad_snoc, binLoad_snoc]
      exact add_to_min_preserves_spread load W (weights (Fin.last T)) b hprior
        (hw (Fin.last T)) (fun k => hmin k (Finset.mem_univ k)) i j

/-- An assignment conserves the total item weight, including zero-weight items. -/
theorem binLoad_sum {T n : ℕ} (weights : Fin T → ℕ)
    (assignment : Fin T → Fin n) :
    (∑ b : Fin n, binLoad weights assignment b) = ∑ t : Fin T, weights t := by
  classical
  unfold binLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _ht
  simp

/-- The spread bound yields the average-load estimate after clearing the
denominator; its slack is one maximum item weight per helper. -/
theorem scaled_load_le_total_add_slack {n : ℕ} (load : Fin n → ℕ) (W : ℕ)
    (hs : HasSpread load W) (i : Fin n) :
    n * load i ≤ (∑ j : Fin n, load j) + n * W := by
  classical
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun j _hj => hs i j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id, Finset.sum_add_distrib] using h

/-- Complete denominator-cleared greedy bound, with an assignment and exact
total-weight conservation. This is valid for arbitrary nonnegative weights. -/
theorem exists_bounded_assignment (n T W : ℕ) (hn : 0 < n)
    (weights : Fin T → ℕ) (hw : ∀ t, weights t ≤ W) :
    ∃ assignment : Fin T → Fin n,
      HasSpread (binLoad weights assignment) W ∧
      (∑ b : Fin n, binLoad weights assignment b) = (∑ t : Fin T, weights t) ∧
      ∀ i : Fin n, n * binLoad weights assignment i ≤
        (∑ t : Fin T, weights t) + n * W := by
  obtain ⟨assignment, hspread⟩ := exists_assignment_spread n T W hn weights hw
  have hsum := binLoad_sum weights assignment
  refine ⟨assignment, hspread, hsum, ?_⟩
  intro i
  simpa only [hsum] using scaled_load_le_total_add_slack
    (binLoad weights assignment) W hspread i

/-- Numerical specialization used for the cluster helper teams: every middle
index has weight at most `2*d`, and their total is at most `2*d^2`. -/
theorem cluster_helper_assignment (helpers T d : ℕ) (hh : 0 < helpers)
    (weights : Fin T → ℕ) (hitem : ∀ t, weights t ≤ 2 * d)
    (htotal : (∑ t : Fin T, weights t) ≤ 2 * d ^ 2) :
    ∃ assignment : Fin T → Fin helpers, ∀ i : Fin helpers,
      helpers * binLoad weights assignment i ≤ 2 * d ^ 2 + helpers * (2 * d) := by
  obtain ⟨assignment, _hs, _ht, hbound⟩ := exists_bounded_assignment helpers T (2 * d) hh weights hitem
  refine ⟨assignment, fun i => (hbound i).trans ?_⟩
  exact Nat.add_le_add_right htotal _

/-- The integer version of the paper's average-plus-one-item bound. -/
theorem exists_assignment_le_average_add (n T B W : ℕ) (hn : 0 < n)
    (weights : Fin T → ℕ) (hitem : ∀ t, weights t ≤ W)
    (htotal : (∑ t : Fin T, weights t) ≤ n * B) :
    ∃ assignment : Fin T → Fin n, ∀ i : Fin n,
      binLoad weights assignment i ≤ B + W := by
  obtain ⟨assignment, _hs, _ht, hbound⟩ := exists_bounded_assignment n T W hn weights hitem
  refine ⟨assignment, fun i => ?_⟩
  apply Nat.le_of_mul_le_mul_left (c := n) (hc := hn)
  calc
    n * binLoad weights assignment i ≤ (∑ t : Fin T, weights t) + n * W := hbound i
    _ ≤ n * B + n * W := Nat.add_le_add_right htotal _
    _ = n * (B + W) := (Nat.mul_add _ _ _).symm

end SparseMM.Balancing
