module

public import FRSB.BridgeDensityDisintegration
public import FRSB.FiniteForwardEndpoint

@[expose] public section

/-! The literal overlap action on continuous paths and its Gaussian-bridge
disintegration. This identifies the actual finite-support diffusion density. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal Topology
namespace FRSB

def forwardPathAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (path : ForwardBridgePath) : ℝ :=
  ∫ t : Overlap, if (t:ℝ) ≤ s then parisiPotential β μ (t,path t) else 0 ∂(μ : Measure Overlap)

set_option maxHeartbeats 800000 in
theorem continuous_forwardPathAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    Continuous (forwardPathAction β μ s) := by
  rw [continuous_iff_continuousAt]
  intro path₀
  apply continuousAt_of_dominated (μ := (μ : Measure Overlap))
    (F := fun (path : ForwardBridgePath) (t : Overlap) =>
      if (t:ℝ) ≤ s then parisiPotential β μ (t,path t) else 0)
    (bound := fun _ : Overlap => β^2+‖path₀‖+1)
  · exact .of_forall fun path => by
      have hc : Continuous (fun t : Overlap => parisiPotential β μ (t,path t)) :=
        (continuous_parisiPotential β μ).comp (continuous_subtype_val.prodMk path.continuous)
      exact (hc.measurable.ite (measurableSet_le (by fun_prop) measurable_const)
        measurable_const).aestronglyMeasurable
  · have hn := (continuous_norm.tendsto path₀).eventually
      (Iio_mem_nhds (lt_add_one ‖path₀‖))
    filter_upwards [hn] with path hp
    exact .of_forall fun t => by
      split_ifs
      · have hu := parisiPotential_absolute_growth β μ t (path t) t.property
        have he := path.norm_coe_le_norm t
        rw [Real.norm_eq_abs] at he ⊢
        linarith
      · rw [norm_zero]
        positivity
  · exact integrable_const _
  · exact .of_forall fun t => by
      by_cases ht : (t:ℝ) ≤ s
      · simp only [ht,ite_true]
        exact ((continuous_parisiPotential β μ).comp
          (continuous_const.prodMk (continuous_eval_const t))).continuousAt
      · simp only [ht,ite_false]
        exact continuousAt_const

def forwardPathWeight (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0:ℝ) 1) (path : ForwardBridgePath) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ
    (s,path ⟨s,hs.1.le,hs.2⟩)-forwardPathAction β μ s path))

theorem measurable_forwardPathWeight (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0:ℝ) 1) : Measurable (forwardPathWeight β μ s hs) := by
  have he : Continuous (fun path : ForwardBridgePath =>
      parisiPotential β μ (s,path ⟨s,hs.1.le,hs.2⟩)) :=
    (continuous_parisiPotential β μ).comp
      (continuous_const.prodMk (continuous_eval_const _))
  exact (Real.continuous_exp.comp ((continuous_const.mul he).sub
    (continuous_forwardPathAction β μ s))).measurable.ennreal_ofReal

theorem forwardPathWeight_bridge (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0:ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardPathWeight β μ s hs (forwardBridgeAsPath β s hs path x) =
      ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x)-
        forwardBridgeAction β μ s hs path x)) := by
  unfold forwardPathWeight
  rw [forwardBridgeAsPath_apply,forwardBridgePoint_at_endpoint]
  congr 3
  apply integral_congr_ae
  exact .of_forall fun t => by
    simp only [forwardPathAction,forwardBridgeAction,forwardBridgeJet,forwardBridgeAsPath_apply,
      pow_zero,one_mul,parisiSpatialField]

theorem forwardPathWeight_scaledBrownian (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0:ℝ) 1) (sample : BrownianSample) :
    forwardPathWeight β μ s hs (scaledBrownianPath β (canonicalBrownianPath sample)) =
      forwardBrownianWeight β μ s.toNNReal sample := by
  unfold forwardPathWeight forwardBrownianWeight
  simp only [scaledBrownianPath,ContinuousMap.smul_apply,smul_eq_mul,canonicalBrownianPath,
    ContinuousMap.coe_mk,Real.coe_toNNReal s hs.1.le]
  congr 3
  unfold forwardPathAction forwardBrownianAction
  apply integral_congr_ae
  exact .of_forall fun t => by
    simp only [scaledBrownianPath,ContinuousMap.smul_apply,smul_eq_mul,canonicalBrownianPath,
      ContinuousMap.coe_mk,Real.coe_toNNReal s hs.1.le]

theorem BrownianTilt_endpoint_eq_bridgeDensity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) :
    (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ s.toNNReal)).map
      (fun sample => β*canonicalBrownian s.toNNReal sample) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) := by
  let R : BrownianSample → ForwardBridgePath :=
    fun sample => scaledBrownianPath β (canonicalBrownianPath sample)
  let E : ForwardBridgePath → ℝ := fun path => path ⟨s,hs.1.le,hs.2⟩
  have hR : Measurable R := (measurable_scaledBrownianPath β).comp measurable_canonicalBrownianPath
  have hE : Measurable E := (continuous_eval_const _).measurable
  have he : E ∘ R = fun sample => β*canonicalBrownian s.toNNReal sample := by
    funext sample
    rfl
  have hw : (fun sample => forwardPathWeight β μ s hs (R sample)) =
      forwardBrownianWeight β μ s.toNNReal := funext (forwardPathWeight_scaledBrownian β μ s hs)
  rw [← hw,← he,← Measure.map_map hE hR,
    map_withDensity_pullback _ R hR _ (measurable_forwardPathWeight β μ s hs)]
  have hmap : canonicalBrownianMeasure.map R = canonicalWienerMeasure.map (scaledBrownianPath β) := by
    rw [canonicalWienerMeasure,Measure.map_map (measurable_scaledBrownianPath β)
      measurable_canonicalBrownianPath]
    rfl
  rw [hmap]
  exact bridge_endpoint_density_of_pullback β hβ μ s hs _
    (measurable_forwardPathWeight β μ s hs) (forwardPathWeight_bridge β μ s hs)

theorem selectedState_endpoint_eq_bridgeDensity_finite (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ s.toNNReal) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) := by
  rw [selectedState_endpoint_eq_BrownianTilt_finite β hβ μ hμ s.toNNReal
    (by simpa only [Real.coe_toNNReal s hs.1.le] using hs.2)]
  exact BrownianTilt_endpoint_eq_bridgeDensity β hβ μ s hs

end FRSB
