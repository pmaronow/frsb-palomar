module

public import FRSB.ForwardExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

/-! Relative derivative bounds across an atom, with a loss linear in its mass. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace FRSB

def atomDerivativeLossRow (K : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (j.choose (i + 1) : ℝ) * exponentialDerivativeConstant K (i + 1)

def atomDerivativeLoss (K : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), atomDerivativeLossRow K j

lemma atomDerivativeLossRow_nonneg (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) (j : ℕ) :
    0 ≤ atomDerivativeLossRow K j :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (exponentialDerivativeConstant_nonneg K hK _))

lemma atomDerivativeLoss_nonneg (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) (k : ℕ) :
    0 ≤ atomDerivativeLoss K k := Finset.sum_nonneg (fun j hj => atomDerivativeLossRow_nonneg K hK j)

lemma atomDerivativeLossRow_le (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) (k j : ℕ) (hj : j ≤ k) :
    atomDerivativeLossRow K j ≤ atomDerivativeLoss K k :=
  Finset.single_le_sum (fun i hi => atomDerivativeLossRow_nonneg K hK i) (Finset.mem_range.mpr (by omega))

set_option maxHeartbeats 1000000 in
/-- Every derivative up to order k of the actual multiplier product has
relative loss at most 1+delta*c_k. The constant is independent of the atom count. -/
theorem atom_relative_derivative_bound (F u : ℝ → ℝ) (δ L : ℝ)
    (hF : ContDiff ℝ ∞ F) (hu : ContDiff ℝ ∞ u) (hδ : δ ∈ Icc (0 : ℝ) 1)
    (hL : 0 ≤ L) (hFnon : ∀ x, 0 ≤ F x) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n)
    (huBound : ∀ n x, ‖iteratedDeriv (n + 1) u x‖ ≤ K (n + 1))
    (k : ℕ) (hrelative : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j F x‖ ≤ L * F x)
    (j : ℕ) (hj : j ≤ k) (x : ℝ) :
    ‖iteratedDeriv j (fun y => F y * Real.exp (-δ * u y)) x‖ ≤
      (1 + δ * atomDerivativeLoss K k) * L * (F x * Real.exp (-δ * u x)) := by
  let E := fun y => Real.exp (-δ * u y)
  have hE : ContDiff ℝ ∞ E := (contDiff_const.mul hu).exp
  have hδ0 : 0 ≤ δ := hδ.1
  have hm : (fun y => F y * E y) = E * F := by funext y; exact mul_comm _ _
  rw [hm, iteratedDeriv_mul (hE.of_le (by simp)).contDiffAt (hF.of_le (by simp)).contDiffAt]
  have hpos (i : ℕ) (hi : i < j) :
      ‖(j.choose (i + 1) : ℝ) * iteratedDeriv (i + 1) E x * iteratedDeriv (j - (i + 1)) F x‖ ≤
        (j.choose (i + 1) : ℝ) * (δ * exponentialDerivativeConstant K (i + 1) * E x) * (L * F x) := by
    have h1 := norm_iteratedDeriv_exp_neg_mul_le_delta u δ hu hδ K hK huBound i x
    have h2 := hrelative (j - (i + 1)) ((Nat.sub_le _ _).trans hj) x
    simp only [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hc := exponentialDerivativeConstant_nonneg K hK (i + 1)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _) (by
      dsimp only [E]
      positivity)
  have hzero : ‖(j.choose 0 : ℝ) * iteratedDeriv 0 E x * iteratedDeriv (j - 0) F x‖ ≤
      E x * (L * F x) := by
    simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, one_mul, Nat.sub_zero,
      norm_mul, E, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hrelative j hj x) (Real.exp_pos _).le
  have hsum : (∑ i ∈ Finset.range j, (j.choose (i + 1) : ℝ) *
      (δ * exponentialDerivativeConstant K (i + 1) * E x) * (L * F x)) =
        δ * atomDerivativeLossRow K j * E x * (L * F x) := by
    unfold atomDerivativeLossRow
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℝ) * iteratedDeriv i E x * iteratedDeriv (j - i) F x‖ := norm_sum_le _ _
    _ = (∑ i ∈ Finset.range j, ‖(j.choose (i + 1) : ℝ) * iteratedDeriv (i + 1) E x * iteratedDeriv (j - (i + 1)) F x‖) +
        ‖(j.choose 0 : ℝ) * iteratedDeriv 0 E x * iteratedDeriv (j - 0) F x‖ := Finset.sum_range_succ' _ j
    _ ≤ (∑ i ∈ Finset.range j, (j.choose (i + 1) : ℝ) * (δ * exponentialDerivativeConstant K (i + 1) * E x) * (L * F x)) +
        E x * (L * F x) := add_le_add (Finset.sum_le_sum (fun i hi => hpos i (Finset.mem_range.mp hi))) hzero
    _ = (1 + δ * atomDerivativeLossRow K j) * L * (F x * E x) := by rw [hsum]; ring
    _ ≤ (1 + δ * atomDerivativeLoss K k) * L * (F x * E x) := by
      have hh := atomDerivativeLossRow_le K hK k j hj
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hδ.1)) hL)
        (mul_nonneg (hFnon x) (Real.exp_pos _).le)

/-- Accumulated linear losses depend only on the total atomic mass. -/
theorem atom_loss_product_le_exp {ι : Type*} (s : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 ≤ δ i) (c : ℝ) (hc : 0 ≤ c) (hmass : ∑ i ∈ s, δ i ≤ 1) :
    (∏ i ∈ s, (1 + c * δ i)) ≤ Real.exp c := by
  calc
    _ ≤ ∏ i ∈ s, Real.exp (c * δ i) := Finset.prod_le_prod₀
      (fun i hi => by have hh := hδ i hi; positivity)
      (fun i hi => by linarith [Real.add_one_le_exp (c * δ i)])
    _ = Real.exp (c * ∑ i ∈ s, δ i) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp c := Real.exp_le_exp.mpr (by nlinarith)

end FRSB
