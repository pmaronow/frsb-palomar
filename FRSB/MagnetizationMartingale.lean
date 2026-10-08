module

public import FRSB.MStochasticL2
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! Literal terminal conditional-expectation and variance identities for
the actual zero-field magnetization process. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal
namespace FRSB

theorem optimalMagnetization_terminal (β : ℝ) (μ : ParisiMeasure) (sample : BrownianSample) :
    M β μ 1 sample = Real.tanh (optimalStateReal β μ sample 1) := by
  simp only [M,jetProcess,parisiSpatialJet_one,parisiGradient_terminal]

theorem condExp_optimalMagnetization_terminal (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ≥0) (hs : s ≤ 1) :
    canonicalBrownianMeasure[(fun sample => Real.tanh (optimalStateReal β μ sample 1)) |
      canonicalBrownianFiltration s] =ᵐ[canonicalBrownianMeasure] M β μ s := by
  have he1 : stoppedMagnetization β hβ μ 1 =
      (fun sample => Real.tanh (optimalStateReal β μ sample 1)) := by
    funext sample
    rw [stoppedMagnetization_eq_physical β hβ μ (by norm_num)]
    exact optimalMagnetization_terminal β μ sample
  have hes : stoppedMagnetization β hβ μ s = M β μ s :=
    funext (stoppedMagnetization_eq_physical β hβ μ hs)
  have he := (martingale_stoppedMagnetization β hβ μ).2 s 1 hs
  rwa [he1,hes] at he

theorem integral_optimalMagnetization_eq_zero (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ≥0) (hs : s ≤ 1) :
    (∫ sample, M β μ s sample ∂canonicalBrownianMeasure) = 0 := by
  have he := (martingale_stoppedMagnetization β hβ μ).2 0 s (show 0 ≤ s from zero_le)
  calc
    _ = ∫ sample, stoppedMagnetization β hβ μ s sample ∂canonicalBrownianMeasure :=
      integral_congr_ae (.of_forall fun sample =>
        (stoppedMagnetization_eq_physical β hβ μ hs sample).symm)
    _ = ∫ sample, canonicalBrownianMeasure[stoppedMagnetization β hβ μ s |
        canonicalBrownianFiltration 0] sample ∂canonicalBrownianMeasure :=
      (integral_condExp (canonicalBrownianFiltration.le 0)).symm
    _ = ∫ sample, stoppedMagnetization β hβ μ 0 sample ∂canonicalBrownianMeasure :=
      integral_congr_ae he
    _ = 0 := by simp only [stoppedMagnetization_initial,integral_zero]

theorem Gamma_eq_variance (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ≥0) (hs : s ≤ 1) :
    Gamma β μ s = variance (M β μ s) canonicalBrownianMeasure := by
  have ht : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨s.coe_nonneg,by exact_mod_cast hs⟩
  rw [variance_eq_integral (measurable_M β μ s ht).aemeasurable,
    integral_optimalMagnetization_eq_zero β hβ μ s hs]
  simp only [Gamma,sub_zero]

end FRSB
