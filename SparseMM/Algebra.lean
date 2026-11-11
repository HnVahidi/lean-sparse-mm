module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Arithmetic correctness of clustered and residual sparse multiplication

The paper's clustered computation partitions the middle indices between team
members. Its residual computation omits terms whose input coordinates are not
allowed by the masks. This file proves both arithmetic identities over an
arbitrary semiring. In particular, multiplication is never commuted.

These identities do not assert communication, load, or scheduling bounds.
-/

@[expose] public section

namespace SparseMM.Algebra

open scoped BigOperators

variable {I J K T R : Type*}

/-- Every input coordinate outside its allowed input mask contains zero.
Marked coordinates are allowed to contain zero as well. -/
def SupportedBy [Zero R] (A : Matrix I J R) (mask : Finset (I × J)) : Prop :=
  ∀ i j, (i, j) ∉ mask → A i j = 0

/-- Potentially contributing middle indices for a requested coordinate. -/
def potentialMiddles [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (aMask : Finset (I × J)) (bMask : Finset (J × K)) (i : I) (k : K) : Finset J :=
  Finset.univ.filter fun j => (i, j) ∈ aMask ∧ (j, k) ∈ bMask

/-- A team member's partial sum. The assignment partitions all middle indices,
including indices whose summands happen to vanish. -/
def partialSum [Fintype J] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R) (assignment : J → T)
    (member : T) (i : I) (k : K) : R :=
  ∑ j ∈ Finset.univ.filter (fun j => assignment j = member), A i j * B j k

/-- The residual computation sums exactly the potential mask triangles. -/
def maskedEntry [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq K]
    [Semiring R] (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K)) (i : I) (k : K) : R :=
  ∑ j ∈ potentialMiddles aMask bMask i k, A i j * B j k

/-- A masked partial sum is also valid when gathering omits unmarked inputs. -/
def maskedPartialSum [Fintype J] [DecidableEq I] [DecidableEq J]
    [DecidableEq K] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (assignment : J → T) (member : T) (i : I) (k : K) : R :=
  ∑ j ∈ (potentialMiddles aMask bMask i k).filter
      (fun j => assignment j = member), A i j * B j k

/-- Regrouping finite summands by a complete assignment neither omits nor
duplicates a middle index. -/
theorem sum_assignment_fibers [Fintype T] [DecidableEq T] [AddCommMonoid R]
    (s : Finset J) (assignment : J → T) (f : J → R) :
    (∑ member : T, ∑ j ∈ s.filter (fun j => assignment j = member), f j) =
      ∑ j ∈ s, f j :=
  Finset.sum_fiberwise s assignment f

/-- Adding all team members' partial sums gives the matrix product entry. -/
theorem partialSums_eq_mul [Fintype J] [Fintype T] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R) (assignment : J → T) (i : I) (k : K) :
    (∑ member : T, partialSum A B assignment member i k) = (A * B) i k := by
  simpa only [partialSum, Matrix.mul_apply] using
    sum_assignment_fibers Finset.univ assignment (fun j => A i j * B j k)

/-- A term outside the intersection of the two input masks vanishes. -/
theorem product_eq_zero_of_not_potential [Fintype J]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (hA : SupportedBy A aMask) (hB : SupportedBy B bMask)
    (i : I) (j : J) (k : K)
    (h : j ∉ potentialMiddles aMask bMask i k) : A i j * B j k = 0 := by
  by_cases ha : (i, j) ∈ aMask
  · have hb : (j, k) ∉ bMask := by
      intro hb
      apply h
      simp only [potentialMiddles, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha, hb⟩
    rw [hB j k hb, mul_zero]
  · rw [hA i j ha, zero_mul]

/-- Omitting all unmarked input-coordinate terms preserves the product entry.
This includes the case where no potential product triangles exist. -/
theorem maskedEntry_eq_mul [Fintype J]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (hA : SupportedBy A aMask) (hB : SupportedBy B bMask) (i : I) (k : K) :
    maskedEntry A B aMask bMask i k = (A * B) i k := by
  unfold maskedEntry
  rw [Matrix.mul_apply]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  exact product_eq_zero_of_not_potential A B aMask bMask hA hB i j k hj

/-- The masked team partial sums equal the residual sum. -/
theorem maskedPartialSums_eq_maskedEntry [Fintype J] [Fintype T]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (assignment : J → T) (i : I) (k : K) :
    (∑ member : T, maskedPartialSum A B aMask bMask assignment member i k) =
      maskedEntry A B aMask bMask i k := by
  exact sum_assignment_fibers (potentialMiddles aMask bMask i k)
    assignment (fun j => A i j * B j k)

/-- Gathering only marked inputs and adding the resulting team sums is correct. -/
theorem maskedPartialSums_eq_mul [Fintype J] [Fintype T]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (hA : SupportedBy A aMask) (hB : SupportedBy B bMask)
    (assignment : J → T) (i : I) (k : K) :
    (∑ member : T, maskedPartialSum A B aMask bMask assignment member i k) =
      (A * B) i k := by
  rw [maskedPartialSums_eq_maskedEntry]
  exact maskedEntry_eq_mul A B aMask bMask hA hB i k

/-- Arithmetic assembly for a requested output mask and a residual subset.
An output may use its own public middle-index assignment. -/
def assembledEntry [Fintype J] [Fintype T]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (requested residual : Finset (I × K)) (assignment : I → K → J → T)
    (i : I) (k : K) : R :=
  if (i, k) ∈ requested then
    if (i, k) ∈ residual then maskedEntry A B aMask bMask i k
    else ∑ member : T, maskedPartialSum A B aMask bMask (assignment i k) member i k
  else 0

/-- Every requested assembled output is exactly the matrix product entry.
This is solely an arithmetic theorem; it does not imply a round bound. -/
theorem assembledEntry_eq_mul [Fintype J] [Fintype T]
    [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq T] [Semiring R]
    (A : Matrix I J R) (B : Matrix J K R)
    (aMask : Finset (I × J)) (bMask : Finset (J × K))
    (hA : SupportedBy A aMask) (hB : SupportedBy B bMask)
    (requested residual : Finset (I × K)) (assignment : I → K → J → T)
    (i : I) (k : K) (hRequested : (i, k) ∈ requested) :
    assembledEntry A B aMask bMask requested residual assignment i k = (A * B) i k := by
  unfold assembledEntry
  rw [ite_eq_left hRequested]
  split_ifs
  · exact maskedEntry_eq_mul A B aMask bMask hA hB i k
  · exact maskedPartialSums_eq_mul A B aMask bMask hA hB (assignment i k) i k

end SparseMM.Algebra
