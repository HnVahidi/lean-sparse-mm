module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM

/-- One more than the integer square root avoids fractional teams and clusters. -/
def teamSize (d : ℕ) : ℕ := Nat.sqrt d + 1

def threshold (d : ℕ) : ℕ := d * teamSize d

theorem teamSize_pos (d : ℕ) : 0 < teamSize d := by
  simp [teamSize]

theorem degree_le_teamSize_sq (d : ℕ) : d ≤ teamSize d * teamSize d := by
  have := Nat.lt_succ_sqrt d
  unfold teamSize
  nlinarith

theorem degree_le_threshold (d : ℕ) : d ≤ threshold d := by
  have := teamSize_pos d
  unfold threshold
  nlinarith

theorem threshold_pos {d : ℕ} (hd : 0 < d) : 0 < threshold d :=
  Nat.mul_pos hd (teamSize_pos d)

/-- The integer threshold has the claimed exponent, with an explicit constant. -/
theorem threshold_le_two_mul_sqrt {d : ℕ} (hd : 0 < d) :
    (threshold d : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt d := by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hnonneg : (0 : ℝ) ≤ d := by positivity
  have hsqr : ((Nat.sqrt d : ℕ) : ℝ) ^ 2 ≤ (d : ℝ) := by
    exact_mod_cast Nat.sqrt_le' d
  have hroot : (Nat.sqrt d : ℝ) ≤ Real.sqrt d :=
    (Real.le_sqrt (by positivity) hnonneg).mpr hsqr
  have hone : (1 : ℝ) ≤ Real.sqrt d := by
    simpa using Real.sqrt_le_sqrt hdreal
  simp only [threshold, teamSize, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith [Real.sqrt_nonneg (d : ℝ)]

end SparseMM
