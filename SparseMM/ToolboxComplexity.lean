module

public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM.ToolboxComplexity

/-- The finite exponential information-growth bound implies the stated
logarithmic lower bound, with an explicit base-dependent constant. -/
theorem log_le_rounds_mul_log {n base T : ℕ} (hn : 0 < n)
    (hbound : n ≤ base ^ T) :
    Real.log (n : ℝ) ≤ (T : ℝ) * Real.log (base : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hreal : (n : ℝ) ≤ (base : ℝ) ^ T := by exact_mod_cast hbound
  simpa only [Real.log_pow] using Real.log_le_log hnreal hreal

theorem log_div_le_rounds {n base T : ℕ} (hn : 0 < n) (hbase : 2 ≤ base)
    (hbound : n ≤ base ^ T) :
    Real.log (n : ℝ) / Real.log (base : ℝ) ≤ (T : ℝ) := by
  have hbasereal : (1 : ℝ) < base := by exact_mod_cast (show 1 < base by omega)
  apply (div_le_iff₀ (Real.log_pos hbasereal)).mpr
  exact log_le_rounds_mul_log hn hbound

/-- Ceiling binary logarithms differ from the real logarithm by at most one.
This includes `n = 1`, where the integer ceiling logarithm is zero. -/
theorem clog_two_le_log_div_add_one {n : ℕ} (hn : 0 < n) :
    (Nat.clog 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hone : n = 1
  · subst n
    simp
  have hnone : 1 < n := by omega
  have hpow := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) hnone
  have hpowreal : (2 : ℝ) ^ (Nat.clog 2 n).pred < (n : ℝ) := by exact_mod_cast hpow
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (Nat.clog 2 n).pred) hpowreal
  rw [Real.log_pow] at hlog
  have hpred : ((Nat.clog 2 n).pred : ℝ) + 1 = (Nat.clog 2 n : ℝ) := by
    exact_mod_cast Nat.succ_pred_eq_of_pos (Nat.clog_pos (by omega : 1 < 2) hnone)
  have hdiv : ((Nat.clog 2 n).pred : ℝ) < Real.log (n : ℝ) / Real.log 2 :=
    (lt_div_iff₀ hlogtwo).mpr hlog
  linarith

/-- The explicit finite pipeline budget has the advertised `O(k + log n)`
form, without an implicit convention for integer logarithms. -/
theorem pipeline_rounds_le {n k : ℕ} (hn : 0 < n) :
    ((2 * k + 2 * Nat.clog 2 n : ℕ) : ℝ) ≤
      2 * (k : ℝ) + (2 / Real.log 2) * Real.log (n : ℝ) + 2 := by
  have hclog := clog_two_le_log_div_add_one hn
  calc
    _ ≤ 2 * (k : ℝ) + 2 * (Real.log (n : ℝ) / Real.log 2 + 1) := by
      push_cast
      linarith
    _ = _ := by ring

/-- For one value and at least two processors, the entire finite pipeline
budget is bounded by a constant times the natural logarithm. -/
theorem single_value_rounds_le_log {n : ℕ} (hn : 2 ≤ n) :
    ((2 + 2 * Nat.clog 2 n : ℕ) : ℝ) ≤
      (6 / Real.log 2) * Real.log (n : ℝ) := by
  have hlogtwo : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hratio : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlogtwo).mpr (by simpa using hlogn)
  have hpipeline := pipeline_rounds_le (k := 1) (show 0 < n by omega)
  norm_num at hpipeline
  have hscale : (6 / Real.log 2) * Real.log (n : ℝ) =
      6 * (Real.log (n : ℝ) / Real.log 2) := by ring
  have hscale' : (2 / Real.log 2) * Real.log (n : ℝ) =
      2 * (Real.log (n : ℝ) / Real.log 2) := by ring
  rw [hscale]
  rw [hscale'] at hpipeline
  push_cast
  linarith

end SparseMM.ToolboxComplexity
