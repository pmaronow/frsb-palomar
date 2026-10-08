module

public import FRSB.ForwardBridge
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

@[expose] public section

/-! Independence of the actual continuous Brownian bridge and its endpoint. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped Topology NNReal
namespace FRSB

def brownianBridgePath (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (sample : BrownianSample) : C(Overlap, ℝ) where
  toFun t := canonicalBrownianPath sample t - forwardBridgeFraction s t *
    canonicalBrownian s.toNNReal sample
  continuous_toFun := (canonicalBrownianPath sample).continuous.sub
    (((continuous_subtype_val.div_const s).min continuous_const).mul continuous_const)

theorem measurable_brownianBridgePath (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Measurable (brownianBridgePath s hs) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact (measurable_canonicalBrownian t.1.toNNReal).sub
    ((measurable_canonicalBrownian s.toNNReal).const_mul _)

theorem covariance_brownianBridge_endpoint (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (t : Overlap) :
    cov[fun sample => brownianBridgePath s hs sample t,
      canonicalBrownian s.toNNReal; canonicalBrownianMeasure] = 0 := by
  have hG := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess
  rw [show (fun sample => brownianBridgePath s hs sample t) =
    (fun sample => canonicalBrownian t.1.toNNReal sample -
      forwardBridgeFraction s t * canonicalBrownian s.toNNReal sample) by rfl,
    covariance_fun_sub_left (hG.hasGaussianLaw_eval _).memLp_two
      ((hG.hasGaussianLaw_eval _).memLp_two.const_mul _) (hG.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left]
  rw [isBrownianReal_canonicalBrownian.toIsPreBrownianReal.covariance_eval,
    isBrownianReal_canonicalBrownian.toIsPreBrownianReal.covariance_eval]
  simp only [min_self, NNReal.coe_min, Real.coe_toNNReal s hs.1.le,
    Real.coe_toNNReal t.1 t.2.1, forwardBridgeFraction]
  by_cases hts : (t : ℝ) ≤ s
  · rw [min_eq_left hts, min_eq_left ((div_le_one hs.1).mpr hts), div_mul_cancel₀ _ hs.1.ne']
    exact sub_self _
  · rw [min_eq_right (le_of_not_ge hts),
      min_eq_right ((one_le_div hs.1).mpr (le_of_not_ge hts)), one_mul]
    exact sub_self _

theorem isGaussianProcess_brownianBridge_endpoint (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    IsGaussianProcess (Sum.elim
      (fun t sample => brownianBridgePath s hs sample t)
      (fun _ : Unit => canonicalBrownian s.toNNReal)) canonicalBrownianMeasure := by
  classical
  apply isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess.of_isGaussianProcess
  intro i
  cases i with
  | inl t =>
    refine ⟨{t.1.toNNReal, s.toNNReal},
      { toFun := fun x => x ⟨t.1.toNNReal, by simp⟩ -
          forwardBridgeFraction s t * x ⟨s.toNNReal, by simp⟩
        map_add' := by intros; simp; ring
        map_smul' := by intros; simp; ring }, ?_⟩
    intro sample
    rfl
  | inr i =>
    refine ⟨{s.toNNReal},
      { toFun := fun x => x ⟨s.toNNReal, by simp⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }, ?_⟩
    intro sample
    rfl

theorem indepFun_brownianBridge_endpoint (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    IndepFun (brownianBridgePath s hs) (canonicalBrownian s.toNNReal)
      canonicalBrownianMeasure := by
  have hp := (isGaussianProcess_brownianBridge_endpoint s hs).indepFun_of_covariance_eq_zero
    (fun t => ((measurable_canonicalBrownian t.1.toNNReal).sub
      ((measurable_canonicalBrownian s.toNNReal).const_mul _)).aemeasurable)
    (fun _ => (measurable_canonicalBrownian s.toNNReal).aemeasurable)
    (fun t _ => covariance_brownianBridge_endpoint s hs t)
  have hp' := hp.comp measurable_id (measurable_pi_apply ())
  rw [IndepFun_iff_Indep] at hp' ⊢
  convert hp' using 1
  have hm : (inferInstance : MeasurableSpace C(Overlap, ℝ)) =
      ⨆ t : Overlap, (inferInstance : MeasurableSpace ℝ).comap (fun path : C(Overlap, ℝ) => path t) :=
    ProbabilityTheory.ContinuousMap.measurableSpace_eq_iSup_comap_eval
  change MeasurableSpace.comap (brownianBridgePath s hs) (inferInstance : MeasurableSpace C(Overlap, ℝ)) = _
  rw [hm, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, Function.comp_def, Function.id_def,
    MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  rfl

def brownianBridgeLaw (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : Measure C(Overlap, ℝ) :=
  canonicalBrownianMeasure.map (brownianBridgePath s hs)

instance brownianBridgeLaw_isProbability (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    IsProbabilityMeasure (brownianBridgeLaw s hs) := by
  unfold brownianBridgeLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_brownianBridgePath s hs).aemeasurable).mpr inferInstance

theorem brownianBridge_endpoint_joint_law (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    canonicalBrownianMeasure.map (fun sample =>
      (brownianBridgePath s hs sample, canonicalBrownian s.toNNReal sample)) =
      (brownianBridgeLaw s hs).prod (gaussianReal 0 s.toNNReal) := by
  rw [(indepFun_brownianBridge_endpoint s hs).map_prod_eq_prod_map_map
    (measurable_brownianBridgePath s hs).aemeasurable
    (measurable_canonicalBrownian s.toNNReal).aemeasurable]
  rw [isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_eval s.toNNReal |>.map_eq]
  rfl

def brownianBridgeReconstruct (s : ℝ) (path : C(Overlap, ℝ)) (y : ℝ) : C(Overlap, ℝ) where
  toFun t := path t + forwardBridgeFraction s t * y
  continuous_toFun := path.continuous.add
    (((continuous_subtype_val.div_const s).min continuous_const).mul continuous_const)

theorem measurable_brownianBridgeReconstruct (s : ℝ) :
    Measurable (fun p : C(Overlap, ℝ) × ℝ => brownianBridgeReconstruct s p.1 p.2) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact ((ProbabilityTheory.ContinuousMap.measurable_iff_eval (fun path : C(Overlap, ℝ) => path)).mp
    measurable_id t |>.comp measurable_fst).add (measurable_snd.const_mul _)

theorem brownianBridge_reconstruct_actual (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (sample : BrownianSample) :
    brownianBridgeReconstruct s (brownianBridgePath s hs sample)
      (canonicalBrownian s.toNNReal sample) = canonicalBrownianPath sample := by
  ext t
  simp only [brownianBridgeReconstruct, brownianBridgePath, ContinuousMap.coe_mk]
  ring

theorem brownianBridge_reconstructed_law (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    ((brownianBridgeLaw s hs).prod (gaussianReal 0 s.toNNReal)).map
      (fun p => brownianBridgeReconstruct s p.1 p.2) = canonicalWienerMeasure := by
  rw [← brownianBridge_endpoint_joint_law s hs,
    Measure.map_map (measurable_brownianBridgeReconstruct s)
      ((measurable_brownianBridgePath s hs).prodMk (measurable_canonicalBrownian s.toNNReal))]
  have heq : (fun p : C(Overlap, ℝ) × ℝ => brownianBridgeReconstruct s p.1 p.2) ∘
      (fun sample => (brownianBridgePath s hs sample, canonicalBrownian s.toNNReal sample)) =
      canonicalBrownianPath := funext (brownianBridge_reconstruct_actual s hs)
  rw [heq]
  rfl

end FRSB
