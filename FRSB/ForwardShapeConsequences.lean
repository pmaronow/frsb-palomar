module

public import FRSB.ForwardHeatShape
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-! The paper's forward third-derivative sign and bounded slope force
convexity of the logarithmic correction.  This deterministic implication
has no unproved density or PDE assumptions. -/
noncomputable section
open Set
open scoped ContDiff
namespace FRSB

lemma second_derivative_nonneg_of_third_nonpos_bounded_slope
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (M : ℝ)
    (hb : ∀ x, |deriv W x| ≤ M)
    (h3 : ∀ x, 0 ≤ x → iteratedDeriv 3 W x ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ iteratedDeriv 2 W x := by
  have hd2 (y : ℝ) : HasDerivAt (iteratedDeriv 2 W) (iteratedDeriv 3 W y) y := by
    have hh := (hW.differentiable_iteratedDeriv 2
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)) y).hasDerivAt
    convert hh using 1
    rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ]
  have hanti : AntitoneOn (iteratedDeriv 2 W) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (hW.continuous_iteratedDeriv 2 (by simp)).continuousOn
      (fun y _ => (hd2 y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hd2 y).deriv]
    have hy0 : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
    exact h3 y hy0.le
  by_contra hn
  have hc : iteratedDeriv 2 W x < 0 := lt_of_not_ge hn
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  let d := (2 * M + 1) / (-iteratedDeriv 2 W x)
  have hd : 0 < d := div_pos (by positivity) (neg_pos.mpr hc)
  have hprod : iteratedDeriv 2 W x * d = -(2 * M + 1) := by
    dsimp [d]
    field_simp [hc.ne]
  have hdiff : Differentiable ℝ (deriv W) := by
    simpa only [iteratedDeriv_one] using hW.differentiable_iteratedDeriv 1 (by simp)
  have hh := (convex_Ici x).image_sub_le_mul_sub_of_deriv_le hdiff.continuous.continuousOn
    hdiff.differentiableOn (C := iteratedDeriv 2 W x)
    (by
      intro y hy
      have hxy : x ≤ y := (interior_subset hy)
      have hy0 : 0 ≤ y := hx.trans hxy
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hanti hx hy0 hxy)
    x (by exact le_refl x) (x + d) (by change x ≤ x + d; linarith) (by linarith)
  rw [show x + d - x = d by ring, hprod] at hh
  have hbx := hb x
  have hby := hb (x + d)
  have hlx := (neg_le_of_abs_le hbx)
  have hly := (neg_le_of_abs_le hby)
  have hux := (le_of_abs_le hbx)
  have huy := (le_of_abs_le hby)
  linarith

lemma second_derivative_nonneg_of_even_third_nonpos_bounded_slope
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (he : ∀ x, W (-x) = W x) (M : ℝ)
    (hb : ∀ x, |deriv W x| ≤ M)
    (h3 : ∀ x, 0 ≤ x → iteratedDeriv 3 W x ≤ 0) (x : ℝ) :
    0 ≤ iteratedDeriv 2 W x := by
  by_cases hx : 0 ≤ x
  · exact second_derivative_nonneg_of_third_nonpos_bounded_slope W hW M hb h3 x hx
  · have hn : 0 ≤ -x := by linarith
    have hh := second_derivative_nonneg_of_third_nonpos_bounded_slope W hW M hb h3 (-x) hn
    have hf : (fun y => W (-y)) = W := funext he
    have hp := iteratedDeriv_comp_neg 2 W x
    rw [hf] at hp
    norm_num only [smul_eq_mul, pow_two, neg_mul_neg, one_mul] at hp
    simpa only [← hp] using hh

end FRSB
