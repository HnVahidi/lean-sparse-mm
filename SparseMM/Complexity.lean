module

public import SparseMM.Rounding

@[expose] public section

namespace SparseMM

/-- Exact sequential budget for the five communication phases.
The public initial input distribution has at most `K*d` entries per machine. -/
def roundBudget (d K : ℕ) : ℕ :=
  2 * max (K * d) (4 * threshold d + d) +
  2 * (4 * threshold d + d) +
  2 * (threshold d + d * teamSize d) +
  2 * (K * d + 2 * d) +
  2 * (threshold d + d)

theorem roundBudget_le (d K : ℕ) :
    roundBudget d K ≤ (4 * K + 40) * threshold d := by
  have hd := degree_le_threshold d
  have hm : max (K * d) (4 * threshold d + d) ≤ K * d + (4 * threshold d + d) :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hk : K * d ≤ K * threshold d := Nat.mul_le_mul_left K hd
  unfold roundBudget
  change 2 * max (K * d) (4 * threshold d + d) +
    2 * (4 * threshold d + d) + 2 * (threshold d + threshold d) +
    2 * (K * d + 2 * d) + 2 * (threshold d + d) ≤ _
  nlinarith

/-- Uniform in `n`: the multiplicative constant depends only on the fixed
constant in the balanced input-distribution assumption. -/
theorem roundBudget_le_sqrt {d : ℕ} (hd : 0 < d) (K : ℕ) :
    (roundBudget d K : ℝ) ≤ (8 * K + 80) * (d : ℝ) * Real.sqrt d := by
  have hround : (roundBudget d K : ℝ) ≤ (4 * K + 40 : ℕ) * (threshold d : ℝ) := by
    exact_mod_cast roundBudget_le d K
  have hthreshold := threshold_le_two_mul_sqrt hd
  have hmul := mul_le_mul_of_nonneg_left hthreshold
    (show (0 : ℝ) ≤ (4 * K + 40 : ℕ) by positivity)
  push_cast at hround hmul
  nlinarith

end SparseMM
