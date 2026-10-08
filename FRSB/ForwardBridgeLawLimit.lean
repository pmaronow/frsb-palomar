module

public import FRSB.ForwardBridgeContinuity

@[expose] public section

/-! Gaussian domination for actual bridge densities and convergence of
their integrals against bounded measurable test functions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped NNReal Topology
namespace FRSB

theorem integrable_gaussian_exp_absolute (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    Integrable (fun x => gaussianPDFReal 0 v x * Real.exp (c + |x|)) := by
  have hi := (ColeHopfFoundation.ProbabilityTheory.integrable_exp_mul_abs_gaussianReal 0 v 1).const_mul
    (Real.exp c)
  rw [gaussianReal_of_var_ne_zero _ hv] at hi
  have hout := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 v) (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)).mp hi
  simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    smul_eq_mul, one_mul, ← Real.exp_add] using hout

theorem integrable_forwardBridge_gaussian_envelope (β : ℝ) (hβ : β ≠ 0)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x) := by
  have hv : (β ^ 2 * s).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1))
  have hi := integrable_gaussian_exp_absolute (β ^ 2 * s).toNNReal hv (β ^ 2)
  have hp : 0 ≤ β ^ 2 * s := mul_nonneg (sq_nonneg β) hs.1.le
  have he : (fun x => gaussianPDFReal 0 (β ^ 2 * s).toNNReal x * Real.exp (β ^ 2 + |x|)) =
      (fun x => Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x) := by
    funext x
    rw [heatDensity_eq_gaussianPDFReal hp]
    rw [mul_comm]
  rw [he] at hi
  exact hi

theorem integrable_forwardBridgeDensity (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : Integrable (forwardBridgeDensity β μ s hs) :=
  (integrable_forwardBridge_gaussian_envelope β hβ s hs).mono'
    (contDiff_forwardBridgeDensity β μ s hs).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (forwardBridgeDensity_pos β hβ μ s hs x).le]
      exact forwardBridgeDensity_gaussian_envelope β μ s hs x)

theorem integrable_forwardBridgeDensity_mul_bounded (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => forwardBridgeDensity β μ s hs x * f x) :=
  (integrable_forwardBridgeDensity β hβ μ s hs).mul_bdd hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem tendsto_integral_forwardBridgeDensity_mul_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun a => ∫ x, forwardBridgeDensity β (ν a) s hs x * f x) l
      (𝓝 (∫ x, forwardBridgeDensity β μ s hs x * f x)) := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0)
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => C * (Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x))
  · exact Filter.Eventually.of_forall fun a =>
      ((contDiff_forwardBridgeDensity β (ν a) s hs).continuous.measurable.mul hf).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_of_nonneg (forwardBridgeDensity_pos β hβ (ν a) s hs x).le]
      have hh := mul_le_mul (forwardBridgeDensity_gaussian_envelope β (ν a) s hs x)
        (hb x) (norm_nonneg _) (by unfold heatDensity; positivity)
      exact hh.trans_eq (mul_comm _ _)
  · exact (integrable_forwardBridge_gaussian_envelope β hβ s hs).const_mul C
  · exact Filter.Eventually.of_forall fun x =>
      (tendsto_forwardBridgeDensity_of_weak β μ ν hν s hs x).mul_const (f x)

end FRSB
