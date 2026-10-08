module

public import FRSB.CrossingActualFields
public import FRSB.CrossingDecay
public import FRSB.CrossingWeightLaw
public import FRSB.ForwardBridgeDensity

@[expose] public section

/-! The actual Gaussian-bridge candidate supplies a genuine normalized
crossing-weight law. Identifying this density with the optimal diffusion
law is a separate theorem; none is assumed or asserted here. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

def bridgeCrossingWeight (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  2 * backwardC β μ (s, x) ^ 2 * forwardBridgeDensity β μ s hs x

theorem bridgeCrossingWeight_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    0 < bridgeCrossingWeight β μ s hs x := by
  unfold bridgeCrossingWeight
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos
    (backwardC_pos β hβ μ s x ⟨hs.1.le, hs.2⟩)))
    (forwardBridgeDensity_pos β hβ μ s hs x)

theorem bridgeCrossingWeight_gaussian_envelope (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : 0 < x) :
    ‖bridgeCrossingWeight β μ s hs x‖ ≤
      (Real.exp (β ^ 2) * (Real.sqrt (2 * Real.pi * (β ^ 2 * s)))⁻¹) *
        crossingGaussianEnvelope (β ^ 2 * s) 0 x := by
  have hC := backwardC_pos β hβ μ s x ⟨hs.1.le, hs.2⟩
  have hC1 := backwardC_le_one β hβ μ s x ⟨hs.1.le, hs.2⟩
  have hCsq : backwardC β μ (s, x) ^ 2 ≤ 1 := by nlinarith
  rw [Real.norm_of_nonneg (bridgeCrossingWeight_pos β hβ μ s hs x).le]
  calc
    bridgeCrossingWeight β μ s hs x ≤ 2 * forwardBridgeDensity β μ s hs x := by
      unfold bridgeCrossingWeight
      nlinarith [forwardBridgeDensity_pos β hβ μ s hs x,
        mul_le_mul_of_nonneg_right hCsq (forwardBridgeDensity_pos β hβ μ s hs x).le]
    _ ≤ 2 * (Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x) :=
      mul_le_mul_of_nonneg_left (forwardBridgeDensity_gaussian_envelope β μ s hs x) (by norm_num)
    _ = _ := by
      unfold crossingGaussianEnvelope heatDensity
      rw [abs_of_pos hx, Real.exp_add, sub_eq_add_neg, Real.exp_add]
      simp only [pow_zero, neg_div]
      ring

theorem bridgeCrossingWeight_integrable (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    IntegrableOn (bridgeCrossingWeight β μ s hs) (Ioi (0 : ℝ)) := by
  apply integrableOn_of_crossingGaussianEnvelope_bound _ (β ^ 2 * s) 0 _
    (mul_pos (sq_pos_of_ne_zero hβ) hs.1)
  · have hc : Continuous (bridgeCrossingWeight β μ s hs) := by
      have hcc : Continuous (fun x => backwardC β μ (s, x)) :=
        continuous_iff_continuousAt.mpr (fun x =>
          (hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le, hs.2⟩).continuousAt)
      unfold bridgeCrossingWeight
      exact (continuous_const.mul (hcc.pow 2)).mul
        (contDiff_forwardBridgeDensity β μ s hs).continuous
    exact hc.aestronglyMeasurable
  · exact fun x hx => bridgeCrossingWeight_gaussian_envelope β hβ μ s hs x hx

theorem bridgeCrossingWeightLaw_isProbability (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    IsProbabilityMeasure (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) :=
  crossingWeightLaw_isProbability _ (bridgeCrossingWeight_integrable β hβ μ s hs)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x)

end FRSB
