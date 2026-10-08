module

public import FRSB.ForwardDensityLaw

@[expose] public section

/-! Literal density statements for the paper's optimal-state definition. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace FRSB

theorem optimalState_endpoint_eq_bridgeDensity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) :
    canonicalBrownianMeasure.map (optimalState β μ s.toNNReal) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) := by
  rw [optimalState_eq_selected β hβ μ]
  exact selectedState_endpoint_eq_bridgeDensity β hβ μ s hs

theorem integral_optimalState_bridgeDensity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    (∫sample,ψ (optimalState β μ s.toNNReal sample) ∂canonicalBrownianMeasure) =
      ∫x,forwardBridgeDensity β μ s hs x*ψ x := by
  rw [optimalState_eq_selected β hβ μ]
  exact integral_selectedState_bridgeDensity β hβ μ s hs ψ hψ

theorem integrable_optimalState_bounded (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ψ : ℝ → ℝ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ x,‖ψ x‖ ≤ C) :
    Integrable (fun sample => ψ (optimalState β μ t sample)) canonicalBrownianMeasure := by
  rw [optimalState_eq_selected β hβ μ]
  exact (integrable_const C).mono'
    (hψ.comp (measurable_selectedParisiState_time β 0 hβ μ t)).aestronglyMeasurable
    (.of_forall fun sample => hC _)

end FRSB
