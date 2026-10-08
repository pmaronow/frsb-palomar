module

public import FRSB.SupportGeometry
public import FRSB.OptimalCurvatureMoment
public import Paper.GaussianPositivity

@[expose] public section

/-! Actual Gaussian state law and positive third-jet energy before the first
point of support. No non-atomic measure or assumed stochastic-law premise is
used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace FRSB
open Paper

theorem optimalState_eq_brownian_before_support (β : ℝ) (μ : ParisiMeasure)
    {a t : ℝ} (hmin : ∀ x ∈ parisiSupport μ, a ≤ x)
    (ht : t ∈ Icc (0 : ℝ) 1) (hta : t ≤ a) (ω : BrownianSample) :
    optimalStateReal β μ ω t = β * canonicalBrownian t.toNNReal ω := by
  rw [optimalState_integral_equation β μ ω ht]
  have hi : (∫ s in 0..t, β ^ 2 * alpha μ s * M β μ s ω) = 0 := by
    calc
      _ = ∫ s in 0..t, (0 : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le ht.1 (fun s hs => by
          rw [alpha, parisiCDF_eq_zero_below_support μ hmin (hs.2.trans_le hta)]
          ring)
      _ = 0 := by simp
  rw [hi, add_zero]

theorem hasLaw_optimalState_before_support (β : ℝ) (μ : ParisiMeasure)
    {a t : ℝ} (hmin : ∀ x ∈ parisiSupport μ, a ≤ x)
    (ht : t ∈ Icc (0 : ℝ) 1) (hta : t ≤ a) :
    HasLaw (fun ω => optimalStateReal β μ ω t)
      (gaussianReal 0 (β ^ 2 * t).toNNReal) canonicalBrownianMeasure := by
  have hl := gaussianReal_const_mul
    (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_eval t.toNNReal) β
  have hv : NNReal.mk (β ^ 2) (sq_nonneg β) * t.toNNReal = (β ^ 2 * t).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ ht.1,
      Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) ht.1)]
  have he : (fun ω => optimalStateReal β μ ω t) =
      fun ω => β * canonicalBrownian t.toNNReal ω :=
    funext (optimalState_eq_brownian_before_support β μ hmin ht hta)
  rw [he]
  simpa only [mul_zero, hv] using hl

/-- A positive Hessian cannot have identically zero derivative while its
primitive is globally bounded. -/
theorem exists_parisiSpatialJet_three_ne_zero (β : ℝ) (μ : ParisiMeasure)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ x : ℝ, parisiSpatialJet β μ 3 t x ≠ 0 := by
  by_contra hn
  push Not at hn
  let c : ℝ := parisiSpatialJet β μ 2 t 0
  have hc : 0 < c := by
    dsimp only [c]
    rw [parisiSpatialJet_two]
    exact parisiHessian_pos_all β μ t 0 ht
  have hconst (x : ℝ) : parisiSpatialJet β μ 2 t x = c := by
    apply is_const_of_deriv_eq_zero
      (fun y => (hasDerivAt_parisiSpatialJet_succ β μ 1 t y).differentiableAt)
      (fun y => by
        rw [(hasDerivAt_parisiSpatialJet_succ β μ 1 t y).deriv]
        exact hn y) x 0
  have hgrad (x : ℝ) :
      parisiGradient β μ (t, x) - c * x = parisiGradient β μ (t, 0) := by
    have hd (y : ℝ) : HasDerivAt (fun z => parisiGradient β μ (t,z) - c * z) 0 y := by
      have hg := hasDerivAt_parisiSpatialJet_succ β μ 0 t y
      change HasDerivAt (fun z => parisiSpatialJet β μ 1 t z)
        (parisiSpatialJet β μ 2 t y) y at hg
      simp only [parisiSpatialJet_one] at hg
      convert hg.sub ((hasDerivAt_id y).const_mul c) using 1
      · funext z
        rfl
      · rw [hconst]
        ring
    have hh := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x 0
    simpa using hh
  have hb0 := norm_parisiGradient_le_one β μ (t, 0)
  have hbx := norm_parisiGradient_le_one β μ (t, 3/c)
  rw [Real.norm_eq_abs, abs_le] at hb0 hbx
  have hg := hgrad (3/c)
  have hcx : c * (3/c) = 3 := by field_simp
  rw [hcx] at hg
  linarith [hb0.1, hbx.2]

theorem thirdMoment2_pos_before_support (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {a t : ℝ} (hmin : ∀ x ∈ parisiSupport μ, a ≤ x)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hta : t ≤ a) :
    0 < ∫ ω, D β μ t ω ^ 2 ∂canonicalBrownianMeasure := by
  let g : ℝ → ℝ := fun x => parisiSpatialJet β μ 3 t x ^ 2
  have hgcont : Continuous g := by
    exact ((continuous_parisiSpatialJet_succ β μ 2).comp
      (continuous_const.prodMk continuous_id)).pow 2
  have hgi : Integrable g (gaussianReal 0 (β ^ 2 * t).toNNReal) := by
    apply (integrable_const
      (‖bcfSpatialDerivative (parisiGradientBCF β μ) 2‖ ^ 2)).mono'
      hgcont.aestronglyMeasurable
    exact .of_forall fun x => by
      change ‖parisiSpatialJet β μ 3 t x ^ 2‖ ≤ _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_parisiSpatialJet_succ_le β μ 2 t x) 2
  obtain ⟨x, hx⟩ := exists_parisiSpatialJet_three_ne_zero β μ ⟨ht.1.le, ht.2⟩
  have hv : (β ^ 2 * t).toNNReal ≠ 0 :=
    (Real.toNNReal_pos.mpr (mul_pos (sq_pos_of_ne_zero hβ) ht.1)).ne'
  have hp := gaussian_integral_pos_of_continuous_nonneg 0 _ hv g hgcont hgi
    (fun x => sq_nonneg _) x (sq_pos_of_ne_zero hx)
  have he := (hasLaw_optimalState_before_support β μ hmin ⟨ht.1.le, ht.2⟩ hta).integral_comp
    hgcont.aestronglyMeasurable
  change (∫ ω, g (optimalStateReal β μ ω t) ∂canonicalBrownianMeasure) = _ at he
  change 0 < ∫ ω, g (optimalStateReal β μ ω t) ∂canonicalBrownianMeasure
  rw [he]
  exact hp

end FRSB
