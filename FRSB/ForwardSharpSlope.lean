module

public import FRSB.ForwardBridgeDensity
public import FRSB.ForwardLeftCurvature

@[expose] public section

/-! The displayed sharp slope estimates use the actual right/left
cumulative masses, rather than only their probability bound by one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped ContDiff Topology
namespace FRSB

 theorem norm_forwardBridgeAction_deriv_le_cdf (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    ‖deriv (forwardBridgeAction β μ s hs path) x‖ ≤ parisiCDF μ s := by
  unfold forwardBridgeAction
  rw [(hasDerivAt_forwardBridgeJet β μ s hs 0 path x).deriv]
  let g : Overlap → ℝ := fun t => if (t : ℝ) ≤ s then 1 else 0
  have hS : MeasurableSet {t : Overlap | (t : ℝ) ≤ s} :=
    measurableSet_le measurable_subtype_coe measurable_const
  have hg : Integrable g (μ : Measure Overlap) := by
    have hconst : Integrable (fun _ : Overlap => (1 : ℝ)) (μ : Measure Overlap) :=
      integrable_const _
    convert! hconst.indicator hS using 1
  have hpoint (t : Overlap) :
      ‖if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 1 *
        parisiSpatialField β μ 1 (t,forwardBridgePoint β s hs path x t) else 0‖ ≤ g t := by
    dsimp [g]
    split_ifs
    · have he : parisiSpatialField β μ 1 = parisiGradient β μ := by
        funext p
        simp only [parisiSpatialField,bcfSpatialDerivative,iteratedDeriv_zero,
          parisiGradient,bcfTranslate_zero]
      rw [he,pow_one]
      change ‖forwardBridgeFraction s t * parisiGradient β μ
        (t,forwardBridgePoint β s hs path x t)‖ ≤ 1
      rw [norm_mul,Real.norm_of_nonneg (forwardBridgeFraction_mem s hs.1 t).1]
      exact (mul_le_mul (forwardBridgeFraction_mem s hs.1 t).2
        (norm_parisiGradient_le_one β μ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simp
  have hi : Integrable (fun t : Overlap => if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 1 *
      parisiSpatialField β μ 1 (t,forwardBridgePoint β s hs path x t) else 0)
      (μ : Measure Overlap) := hg.mono'
        (measurable_forwardBridgeJet_integrand β μ s hs 1 path x).aestronglyMeasurable
        (.of_forall hpoint)
  have hh := (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hg hpoint)
  exact hh.trans_eq (by
    change (∫ t, ({t : Overlap | (t : ℝ) ≤ s}).indicator (fun _ => (1 : ℝ)) t
      ∂(μ : Measure Overlap)) = parisiCDF μ s
    rw [integral_indicator hS]
    simp only [setIntegral_const,smul_eq_mul,mul_one,Measure.real,parisiCDF])

 theorem forwardBridgeFactor_first_relative_bound_cdf (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖deriv (forwardBridgeFactor β μ s hs) x‖ ≤ parisiCDF μ s*forwardBridgeFactor β μ s hs x := by
  have hpoint (path : ForwardBridgePath) :
      ‖iteratedDeriv 1 (forwardBridgePathFactor β μ s hs path) x‖ ≤
        parisiCDF μ s*forwardBridgePathFactor β μ s hs path x := by
    have hh := ((contDiff_forwardBridgeAction β μ s hs path).differentiable
      (by simp) x).hasDerivAt.neg.exp
    change HasDerivAt (forwardBridgePathFactor β μ s hs path) _ x at hh
    rw [iteratedDeriv_one,hh.deriv,norm_mul,norm_neg,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hi := mul_le_mul_of_nonneg_left
      (norm_forwardBridgeAction_deriv_le_cdf β μ s hs path x)
      (forwardBridgePathFactor_pos β μ s hs path x).le
    simpa only [forwardBridgePathFactor,Pi.neg_apply,mul_comm] using hi
  have hi : Integrable (fun path => iteratedDeriv 1 (forwardBridgePathFactor β μ s hs path) x)
      canonicalWienerMeasure := ((integrable_forwardBridgePathFactor β μ s hs x).const_mul
        (parisiCDF μ s)).mono'
    (((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs 1).comp
      (show Continuous (fun path : ForwardBridgePath => (path,x)) by fun_prop)).aestronglyMeasurable)
    (.of_forall hpoint)
  rw [←iteratedDeriv_one,iteratedDeriv_forwardBridgeFactor]
  have hh := (norm_integral_le_integral_norm _).trans
    (integral_mono hi.norm ((integrable_forwardBridgePathFactor β μ s hs x).const_mul _) hpoint)
  rw [integral_const_mul] at hh
  exact hh

 theorem forwardBridgeCorrection_slope_bound_cdf (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖deriv (forwardBridgeCorrection β μ s hs) x‖ ≤ parisiCDF μ s := by
  have h := ((contDiff_forwardBridgeFactor β μ s hs).differentiable (by simp) x).hasDerivAt.log
    (forwardBridgeFactor_pos β μ s hs x).ne' |>.neg
  change HasDerivAt (forwardBridgeCorrection β μ s hs) _ x at h
  rw [h.deriv,norm_neg,norm_div,Real.norm_of_nonneg (forwardBridgeFactor_pos β μ s hs x).le]
  exact (div_le_iff₀ (forwardBridgeFactor_pos β μ s hs x)).mpr
    (forwardBridgeFactor_first_relative_bound_cdf β μ s hs x)

end FRSB
