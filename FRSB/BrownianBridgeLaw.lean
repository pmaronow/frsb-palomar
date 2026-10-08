module

public import FRSB.BrownianBridge

@[expose] public section

/-! Gaussian endpoint disintegration of the actual scaled Brownian path law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal
namespace FRSB

def bridgeResidual (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : C(Overlap, ℝ)) : C(Overlap, ℝ) where
  toFun t := path t - forwardBridgeFraction s t * path ⟨s, hs.1.le, hs.2⟩
  continuous_toFun := path.continuous.sub
    (((continuous_subtype_val.div_const s).min continuous_const).mul continuous_const)

theorem measurable_bridgeResidual (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Measurable (bridgeResidual s hs) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  have hm := (ProbabilityTheory.ContinuousMap.measurable_iff_eval
    (fun path : C(Overlap, ℝ) => path)).mp measurable_id
  exact (hm t).sub ((hm ⟨s, hs.1.le, hs.2⟩).const_mul _)

theorem brownianBridgeLaw_eq_wienerMap (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    brownianBridgeLaw s hs = canonicalWienerMeasure.map (bridgeResidual s hs) := by
  rw [canonicalWienerMeasure, Measure.map_map (measurable_bridgeResidual s hs)
    measurable_canonicalBrownianPath]
  apply congrArg (fun f => canonicalBrownianMeasure.map f)
  funext sample
  ext t
  simp only [Function.comp_def, bridgeResidual, brownianBridgePath,
    ContinuousMap.coe_mk, canonicalBrownianPath, Real.coe_toNNReal s hs.1.le]

def scaledBrownianPath (β : ℝ) (path : C(Overlap, ℝ)) : C(Overlap, ℝ) := β • path

theorem measurable_scaledBrownianPath (β : ℝ) : Measurable (scaledBrownianPath β) := by
  unfold scaledBrownianPath
  exact ((continuous_const : Continuous (fun _ : C(Overlap, ℝ) => β)).smul continuous_id).measurable

def bridgeRealization (β s : ℝ) (path : C(Overlap, ℝ)) (x : ℝ) : C(Overlap, ℝ) where
  toFun t := forwardBridgeFraction s t * x + β * path t
  continuous_toFun := (((continuous_subtype_val.div_const s).min continuous_const).mul
    continuous_const).add (continuous_const.mul path.continuous)

theorem measurable_bridgeRealization (β s : ℝ) :
    Measurable (fun p : C(Overlap, ℝ) × ℝ => bridgeRealization β s p.1 p.2) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  have hm := (ProbabilityTheory.ContinuousMap.measurable_iff_eval
    (fun path : C(Overlap, ℝ) => path)).mp measurable_id
  exact (measurable_snd.const_mul _).add ((hm t).comp measurable_fst |>.const_mul β)

def forwardBridgeAsPath (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : C(Overlap, ℝ)) (x : ℝ) : C(Overlap, ℝ) :=
  bridgeRealization β s (bridgeResidual s hs path) x

theorem forwardBridgeAsPath_apply (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (path : C(Overlap, ℝ)) (x : ℝ) (t : Overlap) :
    forwardBridgeAsPath β s hs path x t = forwardBridgePoint β s hs path x t := rfl

theorem measurable_forwardBridgeAsPath (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Measurable (fun p : C(Overlap, ℝ) × ℝ => forwardBridgeAsPath β s hs p.1 p.2) :=
  (measurable_bridgeRealization β s).comp
    (((measurable_bridgeResidual s hs).comp measurable_fst).prodMk measurable_snd)

theorem hasLaw_scaled_brownian_endpoint (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    HasLaw (fun sample => β * canonicalBrownian s.toNNReal sample)
      (gaussianReal 0 (β ^ 2 * s).toNNReal) canonicalBrownianMeasure := by
  have hh := gaussianReal_const_mul
    (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_eval s.toNNReal) β
  convert hh using 1
  congr 1
  · ring
  · apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal s hs.1.le,
      Real.coe_toNNReal (β^2*s) (mul_nonneg (sq_nonneg β) hs.1.le)]

theorem brownianBridge_scaled_endpoint_joint_law (β s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    canonicalBrownianMeasure.map (fun sample =>
      (brownianBridgePath s hs sample, β * canonicalBrownian s.toNNReal sample)) =
      (brownianBridgeLaw s hs).prod (gaussianReal 0 (β ^ 2 * s).toNNReal) := by
  have hi := (indepFun_brownianBridge_endpoint s hs).comp measurable_id
    ((measurable_const : Measurable (fun _ : ℝ => β)).mul measurable_id)
  rw [hi.map_prod_eq_prod_map_map
    (measurable_brownianBridgePath s hs).aemeasurable
    ((measurable_canonicalBrownian s.toNNReal).const_mul β).aemeasurable,
    (hasLaw_scaled_brownian_endpoint β s hs).map_eq]
  rfl

theorem forwardBridge_scaled_wiener_law (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (canonicalWienerMeasure.prod (gaussianReal 0 (β ^ 2 * s).toNNReal)).map
      (fun p => forwardBridgeAsPath β s hs p.1 p.2) =
      canonicalWienerMeasure.map (scaledBrownianPath β) := by
  have hleft : (canonicalWienerMeasure.prod (gaussianReal 0 (β^2*s).toNNReal)).map
      (fun p => forwardBridgeAsPath β s hs p.1 p.2) =
      ((brownianBridgeLaw s hs).prod (gaussianReal 0 (β^2*s).toNNReal)).map
        (fun p => bridgeRealization β s p.1 p.2) := by
    rw [brownianBridgeLaw_eq_wienerMap s hs,
      ← Measure.map_id (μ := gaussianReal 0 (β^2*s).toNNReal),
      Measure.map_prod_map _ _ (measurable_bridgeResidual s hs) measurable_id,
      Measure.map_map (measurable_bridgeRealization β s)
        ((measurable_bridgeResidual s hs).prodMap measurable_id)]
    rw [Measure.map_id]
    rfl
  rw [hleft, ← brownianBridge_scaled_endpoint_joint_law β s hs,
    Measure.map_map (measurable_bridgeRealization β s)
      ((measurable_brownianBridgePath s hs).prodMk
        ((measurable_canonicalBrownian s.toNNReal).const_mul β)),
    canonicalWienerMeasure, Measure.map_map (measurable_scaledBrownianPath β)
      measurable_canonicalBrownianPath]
  apply congrArg (fun f => canonicalBrownianMeasure.map f)
  funext sample
  ext t
  simp only [Function.comp_def, bridgeRealization, brownianBridgePath,
    ContinuousMap.coe_mk, scaledBrownianPath, ContinuousMap.smul_apply, smul_eq_mul]
  ring

end FRSB
