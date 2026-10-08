module

public import FRSB.BridgePathWeight
public import FRSB.ForwardBridgeLawLimit
public import FRSB.ForwardStateLawLimit

@[expose] public section

/-! The genuine forward density of the constructed optimal diffusion for
arbitrary overlap probability measures, obtained from actual finite laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped NNReal ENNReal Topology
namespace FRSB

def forwardDensityMeasure (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0:ℝ) 1) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x))

theorem isFiniteMeasure_forwardDensityMeasure (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) : IsFiniteMeasure (forwardDensityMeasure β μ s hs) :=
  isFiniteMeasure_withDensity_ofReal (integrable_forwardBridgeDensity β hβ μ s hs).hasFiniteIntegral

theorem integral_forwardDensityMeasure (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) (ψ : ℝ → ℝ) :
    (∫x,ψ x ∂forwardDensityMeasure β μ s hs) =
      ∫x,forwardBridgeDensity β μ s hs x*ψ x := by
  rw [forwardDensityMeasure,integral_withDensity_eq_integral_toReal_smul
    (contDiff_forwardBridgeDensity β μ s hs).continuous.measurable.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top) ψ]
  apply integral_congr_ae
  exact .of_forall fun x => by
    change (ENNReal.ofReal (forwardBridgeDensity β μ s hs x)).toReal * ψ x = _
    rw [ENNReal.toReal_ofReal (forwardBridgeDensity_pos β hβ μ s hs x).le]

theorem integral_selectedState_bridgeDensity_finite (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    (∫sample,ψ (selectedParisiItoState β 0 hβ μ s.toNNReal sample) ∂canonicalBrownianMeasure) =
      ∫x,forwardBridgeDensity β μ s hs x*ψ x := by
  have he := congrArg (fun Q : Measure ℝ => ∫x,ψ x ∂Q)
    (selectedState_endpoint_eq_bridgeDensity_finite β hβ μ hμ s hs)
  rw [integral_map (measurable_selectedParisiState_time β 0 hβ μ _).aemeasurable
    hψ.aestronglyMeasurable] at he
  exact he.trans (integral_forwardDensityMeasure β hβ μ s hs ψ)

theorem integral_selectedState_bridgeDensity_continuous (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (C : ℝ) (hC : ∀ x,‖ψ x‖ ≤ C) :
    (∫sample,ψ (selectedParisiItoState β 0 hβ μ s.toNNReal sample) ∂canonicalBrownianMeasure) =
      ∫x,forwardBridgeDensity β μ s hs x*ψ x := by
  have hμ := tendsto_preservingMeasure μ ∅
  have hstate := tendsto_integral_selectedState_of_weak β hβ (preservingMeasure μ ∅) μ hμ
    s.toNNReal (by simpa only [Real.coe_toNNReal s hs.1.le] using hs.2) ψ hψ C hC
  have hdensity := tendsto_integral_forwardBridgeDensity_mul_of_weak β hβ μ (preservingMeasure μ ∅)
    hμ s hs ψ hψ.measurable C hC
  have he : (fun n => ∫sample,ψ (selectedParisiItoState β 0 hβ (preservingMeasure μ ∅ n)
      s.toNNReal sample) ∂canonicalBrownianMeasure) =
      fun n => ∫x,forwardBridgeDensity β (preservingMeasure μ ∅ n) s hs x*ψ x := by
    funext n
    exact integral_selectedState_bridgeDensity_finite β hβ _ (finite_support_preservingMeasure μ ∅ n)
      s hs ψ hψ.measurable
  rw [he] at hstate
  exact tendsto_nhds_unique hstate hdensity

/-- The candidate Gaussian-bridge expression is the actual endpoint density
for every overlap probability measure. No density-law assumption is supplied. -/
theorem selectedState_endpoint_eq_bridgeDensity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ s.toNNReal) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) := by
  haveI := isFiniteMeasure_forwardDensityMeasure β hβ μ s hs
  change (_ : Measure ℝ) = forwardDensityMeasure β μ s hs
  apply measure_eq_of_cos_sin_integrals
  · intro ξ
    rw [integral_map (measurable_selectedParisiState_time β 0 hβ μ _).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.cos (ξ*x)) _),
      integral_forwardDensityMeasure β hβ μ s hs]
    exact integral_selectedState_bridgeDensity_continuous β hβ μ s hs
      (fun x => Real.cos (ξ*x)) (by fun_prop) 1
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ*x))
  · intro ξ
    rw [integral_map (measurable_selectedParisiState_time β 0 hβ μ _).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Real.sin (ξ*x)) _),
      integral_forwardDensityMeasure β hβ μ s hs]
    exact integral_selectedState_bridgeDensity_continuous β hβ μ s hs
      (fun x => Real.sin (ξ*x)) (by fun_prop) 1
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ*x))

theorem isProbabilityMeasure_forwardDensityMeasure (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) :
    IsProbabilityMeasure (forwardDensityMeasure β μ s hs) := by
  rw [forwardDensityMeasure,←selectedState_endpoint_eq_bridgeDensity β hβ μ s hs]
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_selectedParisiState_time β 0 hβ μ _).aemeasurable).mpr inferInstance

/-- Literal integration of every bounded Borel observable against the
constructed optimal-state forward density. -/
theorem integral_selectedState_bridgeDensity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    (∫sample,ψ (selectedParisiItoState β 0 hβ μ s.toNNReal sample) ∂canonicalBrownianMeasure) =
      ∫x,forwardBridgeDensity β μ s hs x*ψ x := by
  have he := congrArg (fun Q : Measure ℝ => ∫x,ψ x ∂Q)
    (selectedState_endpoint_eq_bridgeDensity β hβ μ s hs)
  rw [integral_map (measurable_selectedParisiState_time β 0 hβ μ _).aemeasurable
    hψ.aestronglyMeasurable] at he
  exact he.trans (integral_forwardDensityMeasure β hβ μ s hs ψ)

theorem integral_forwardBridgeDensity_eq_one (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) :
    (∫x,forwardBridgeDensity β μ s hs x) = 1 := by
  have he := integral_selectedState_bridgeDensity β hβ μ s hs (fun _ => 1) measurable_const
  simpa [Measure.real] using he.symm

end FRSB
