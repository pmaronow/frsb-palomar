module

public import FRSB.FiniteForwardEndpoint
public import FRSB.DiffusionApproximation

@[expose] public section

/-! Weak overlap convergence gives genuine bounded-continuous endpoint
observable convergence for the constructed common-Brownian optimal states. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped Topology NNReal
namespace FRSB

theorem tendsto_optimalStateReal_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (μs : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) (sample : BrownianSample) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => optimalStateReal β (μs i) sample t) L
      (nhds (optimalStateReal β μ sample t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [optimalState_uniform_convergence_of_weak β μs μ hμ ε hε] with i hi
  simpa only [dist_eq_norm] using hi sample t ht

theorem measurable_optimalStateReal_time (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Measurable (fun sample => optimalStateReal β μ sample t) := by
  have hm := measurable_selectedParisiState_time β 0 hβ μ t.toNNReal
  have he : optimalState β μ t.toNNReal = fun sample => optimalStateReal β μ sample t := by
    funext sample
    rw [optimalState_eq_real β μ (by simpa only [Real.coe_toNNReal _ ht.1] using ht.2),
      Real.coe_toNNReal _ ht.1]
  rw [←he,optimalState_eq_selected β hβ μ]
  exact hm

/-- The terminal law limit is tested by actual bounded continuous functions;
this suffices in particular for the characteristic-function identification. -/
theorem tendsto_integral_optimalStateReal_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0) (μs : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Tendsto (fun i => ∫sample,ψ (optimalStateReal β (μs i) sample t) ∂canonicalBrownianMeasure) L
      (nhds (∫sample,ψ (optimalStateReal β μ sample t) ∂canonicalBrownianMeasure)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => C)
  · exact .of_forall fun i =>
      (hψ.measurable.comp (measurable_optimalStateReal_time β hβ (μs i) ht)).aestronglyMeasurable
  · exact .of_forall fun _ => .of_forall fun sample => hC _
  · exact integrable_const C
  · exact .of_forall fun sample => hψ.continuousAt.tendsto.comp
      (tendsto_optimalStateReal_of_weak β μs μ hμ sample ht)

theorem tendsto_integral_selectedState_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0) (μs : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    Tendsto (fun i => ∫sample,ψ (selectedParisiItoState β 0 hβ (μs i) t sample) ∂canonicalBrownianMeasure) L
      (nhds (∫sample,ψ (selectedParisiItoState β 0 hβ μ t sample) ∂canonicalBrownianMeasure)) := by
  have he (ν : ParisiMeasure) :
      selectedParisiItoState β 0 hβ ν t = fun sample => optimalStateReal β ν sample t := by
    rw [←optimalState_eq_selected β hβ ν]
    funext sample
    exact optimalState_eq_real β ν ht sample
  simp_rw [he]
  exact tendsto_integral_optimalStateReal_of_weak β hβ μs μ hμ ⟨t.coe_nonneg,ht⟩ ψ hψ C hC

end FRSB
