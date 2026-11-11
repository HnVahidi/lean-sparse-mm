module

public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace SparseMM.BooleanDegree

open scoped BigOperators

abbrev Cube (n : ℕ) := Fin n → Bool

def DependsOn {n : ℕ} (s : Finset (Fin n)) (f : Cube n → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y

def Space (n k : ℕ) : Submodule ℝ (Cube n → ℝ) :=
  Submodule.span ℝ {f | ∃ s : Finset (Fin n), s.card ≤ k ∧ DependsOn s f}

theorem of_dependsOn {n k : ℕ} {s : Finset (Fin n)} {f : Cube n → ℝ}
    (hs : s.card ≤ k) (hf : DependsOn s f) : f ∈ Space n k :=
  Submodule.subset_span ⟨s, hs, hf⟩

theorem mono {n k l : ℕ} (hkl : k ≤ l) : Space n k ≤ Space n l := by
  apply Submodule.span_mono
  rintro f ⟨s, hs, hf⟩
  exact ⟨s, hs.trans hkl, hf⟩

theorem const {n k : ℕ} (c : ℝ) : (fun _ : Cube n => c) ∈ Space n k :=
  of_dependsOn (s := ∅) (by simp) (by intro x y _; rfl)

theorem add {n k : ℕ} {f g : Cube n → ℝ}
    (hf : f ∈ Space n k) (hg : g ∈ Space n k) : (f + g) ∈ Space n k :=
  (Space n k).add_mem hf hg

theorem sub {n k : ℕ} {f g : Cube n → ℝ}
    (hf : f ∈ Space n k) (hg : g ∈ Space n k) : (f - g) ∈ Space n k :=
  (Space n k).sub_mem hf hg

theorem sum {n k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cube n → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Space n k) : (∑ i ∈ s, f i) ∈ Space n k :=
  Submodule.sum_mem _ hf

theorem dependsOn_mul {n : ℕ} {s t : Finset (Fin n)} {f g : Cube n → ℝ}
    (hf : DependsOn s f) (hg : DependsOn t g) : DependsOn (s ∪ t) (f * g) := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
    hg x y (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem mul {n k l : ℕ} {f g : Cube n → ℝ}
    (hf : f ∈ Space n k) (hg : g ∈ Space n l) : f * g ∈ Space n (k + l) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨s, hs, hf⟩
      induction hg using Submodule.span_induction with
      | mem g hg =>
          rcases hg with ⟨t, ht, hg⟩
          exact of_dependsOn ((Finset.card_union_le s t).trans (Nat.add_le_add hs ht))
            (dependsOn_mul hf hg)
      | zero => simp
      | add g g' _ _ ih ih' => simpa only [mul_add] using (Space n (k + l)).add_mem ih ih'
      | smul c g _ ih => simpa only [mul_smul_comm] using (Space n (k + l)).smul_mem c ih
  | zero => simpa using (Space n (k + l)).zero_mem
  | add f f' _ _ ih ih' => simpa only [add_mul] using (Space n (k + l)).add_mem ih ih'
  | smul c f _ ih => simpa only [smul_mul_assoc] using (Space n (k + l)).smul_mem c ih

def sign {n : ℕ} (x : Cube n) : ℝ := ∏ i, if x i then (-1 : ℝ) else 1

def alternating (n : ℕ) : (Cube n → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ x : Cube n, sign x * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

def toggle {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (! x i)

def toggleEquiv {n : ℕ} (i : Fin n) : Cube n ≃ Cube n where
  toFun := toggle i
  invFun := toggle i
  left_inv x := by
    funext j
    by_cases hj : j = i
    · subst j; simp [toggle]
    · simp [toggle, hj]
  right_inv x := by
    funext j
    by_cases hj : j = i
    · subst j; simp [toggle]
    · simp [toggle, hj]

theorem sign_toggle {n : ℕ} (i : Fin n) (x : Cube n) : sign (toggle i x) = - sign x := by
  classical
  unfold sign
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have heq : (∏ j ∈ Finset.univ.erase i, if toggle i x j then (-1 : ℝ) else 1) =
      ∏ j ∈ Finset.univ.erase i, if x j then (-1 : ℝ) else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [toggle, Finset.ne_of_mem_erase hj]
  rw [heq]
  cases hx : x i <;> simp [toggle, hx]

theorem alternating_dependsOn {n : ℕ} {s : Finset (Fin n)} {f : Cube n → ℝ}
    (hs : s.card < n) (hf : DependsOn s f) : alternating n f = 0 := by
  classical
  have hcard : s.card < (Finset.univ : Finset (Fin n)).card := by simpa using hs
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hsame (x : Cube n) : f (toggle i x) = f x := by
    apply hf
    intro j hj
    have hji : j ≠ i := by intro he; subst j; exact hi hj
    simp [toggle, hji]
  have hsum := (toggleEquiv i).sum_comp (fun x : Cube n => sign x * f x)
  have hneg : alternating n f = - alternating n f := by
    change (∑ x : Cube n, sign x * f x) = - ∑ x : Cube n, sign x * f x
    calc
      _ = ∑ x : Cube n, sign (toggle i x) * f (toggle i x) := hsum.symm
      _ = ∑ x : Cube n, -(sign x * f x) := by simp_rw [sign_toggle, hsame, neg_mul]
      _ = _ := by rw [Finset.sum_neg_distrib]
  linarith

theorem alternating_space {n k : ℕ} (hkn : k < n) {f : Cube n → ℝ}
    (hf : f ∈ Space n k) : alternating n f = 0 := by
  have hspan : Space n k ≤ (alternating n).ker := by
    apply Submodule.span_le.mpr
    rintro g ⟨s, hs, hg⟩
    exact alternating_dependsOn (hs.trans_lt hkn) hg
  exact hspan hf

def orValue {n : ℕ} (x : Cube n) : ℝ := if ∃ i, x i = true then 1 else 0

theorem orValue_eq {n : ℕ} (x : Cube n) :
    orValue x = 1 - (if x = (fun _ => false) then (1 : ℝ) else 0) := by
  classical
  by_cases hx : x = fun _ => false
  · subst x; simp [orValue]
  · have ht : ∃ i, x i = true := by
      by_contra hn
      apply hx
      funext i
      cases hi : x i
      · rfl
      · exact (hn ⟨i, hi⟩).elim
    simp [orValue, ht, hx]

theorem alternating_orValue {n : ℕ} (hn : 0 < n) :
    alternating n (orValue (n := n)) = -1 := by
  have hconst : alternating n (fun _ : Cube n => (1 : ℝ)) = 0 :=
    alternating_dependsOn (s := ∅) (by simpa using hn) (by intro x y _; rfl)
  have hdelta : alternating n (fun x : Cube n => if x = (fun _ => false) then (1 : ℝ) else 0) = 1 := by
    classical
    simp [alternating, sign]
  have heq : orValue (n := n) =
      (fun _ : Cube n => (1 : ℝ)) - (fun x => if x = (fun _ => false) then (1 : ℝ) else 0) := by
    funext x
    exact orValue_eq x
  rw [heq, map_sub, hconst, hdelta]
  norm_num

/-- OR on n independent Boolean inputs has full degree in the cylinder span. -/
theorem or_requires_degree {n k : ℕ} (h : orValue (n := n) ∈ Space n k) : n ≤ k := by
  by_contra hn
  have hkn : k < n := Nat.lt_of_not_ge hn
  have hz := alternating_space hkn h
  have hv := alternating_orValue (show 0 < n by omega)
  linarith

def flipCube {n : ℕ} (x : Cube n) : Cube n := fun i => !x i

theorem flip_mem {n k : ℕ} {f : Cube n → ℝ} (hf : f ∈ Space n k) :
    (fun x => f (flipCube x)) ∈ Space n k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨s, hs, hf⟩
      apply of_dependsOn hs
      intro x y hxy
      apply hf
      intro i hi
      simp only [flipCube, hxy i hi]
  | zero =>
      change (0 : Cube n → ℝ) ∈ Space n k
      exact (Space n k).zero_mem
  | add f g _ _ ih ih' => exact (Space n k).add_mem ih ih'
  | smul c f _ ih => exact (Space n k).smul_mem c ih

def andValue {n : ℕ} (x : Cube n) : ℝ := if ∀ i, x i = true then 1 else 0

theorem orValue_eq_one_sub_and_flip {n : ℕ} :
    orValue (n := n) = (fun _ : Cube n => (1 : ℝ)) - (fun x => andValue (flipCube x)) := by
  classical
  funext x
  by_cases ht : ∃ i, x i = true
  · obtain ⟨i, hi⟩ := ht
    have hnot : ¬∀ j, flipCube x j = true := by
      intro hh
      have := hh i
      simp [flipCube, hi] at this
    simp [orValue, andValue, hnot, show ∃ j, x j = true from ⟨i, hi⟩]
  · have hall : ∀ j, flipCube x j = true := by
      intro j
      cases hj : x j
      · simp [flipCube, hj]
      · exact (ht ⟨j, hj⟩).elim
    simp [orValue, andValue, ht, hall]

theorem and_requires_degree {n k : ℕ} (h : andValue (n := n) ∈ Space n k) : n ≤ k := by
  apply or_requires_degree
  rw [orValue_eq_one_sub_and_flip]
  exact sub (const 1) (flip_mem h)

end SparseMM.BooleanDegree
