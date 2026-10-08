module

public import FRSB.ForwardLeftAtoms
public import FRSB.ConstantMassGrowthRefined
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The literal origin bound in display 4.8, from the actual Gaussian
bridge second moment and Jensen's inequality for its positive action. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000

theorem logCosh_le_square_half (x : ℝ) : Real.log (Real.cosh x) ≤ x^2/2 := by
  have htanh (y : ℝ) (hy : 0 ≤ y) : Real.tanh y ≤ y := by
    have hm := monotone_of_hasDerivAt_nonneg
      (fun y => (hasDerivAt_id y).sub (hasDerivAt_tanh y))
      (fun y => sub_nonneg.mpr (sech_sq_le_one y))
    simpa only [Pi.sub_apply,id_eq,Real.tanh_zero,sub_zero,sub_nonneg] using hm hy
  have hm : MonotoneOn (fun y => y^2/2-Real.log (Real.cosh y)) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact ((continuous_id.pow 2).div_const 2 |>.sub
        (Real.continuous_cosh.log (fun y => (Real.cosh_pos y).ne'))).continuousOn
    · intro y hy
      exact (((hasDerivAt_id y).pow 2).div_const 2 |>.sub (hasDerivAt_log_cosh y)).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := interior_subset hy
      have hh := htanh y hy0
      dsimp
      nlinarith
  have hh := hm (show (0 : ℝ) ∈ Ici 0 by simp) (abs_nonneg x) (abs_nonneg x)
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),zero_div,Real.cosh_zero,Real.log_one,sub_self] at hh
  have he : Real.cosh |x| = Real.cosh x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,Real.cosh_neg]
  rw [he,sq_abs] at hh
  linarith

theorem brownian_linear_combination_square (β θ : ℝ) (t s : ℝ≥0) :
    (∫ sample,(β*(canonicalBrownian t sample-θ*canonicalBrownian s sample))^2
      ∂canonicalBrownianMeasure) = β^2*((t : ℝ)-2*θ*(min t s : ℝ)+θ^2*(s : ℝ)) := by
  let hB := isBrownianReal_canonicalBrownian.toIsPreBrownianReal
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hz := (ht.sub (hs.const_mul θ)).const_mul β
  have hmean : (∫ sample,β*(canonicalBrownian t sample-θ*canonicalBrownian s sample)
      ∂canonicalBrownianMeasure)=0 := by
    rw [integral_const_mul,integral_sub (ht.integrable (by norm_num))
      ((hs.const_mul θ).integrable (by norm_num)),integral_const_mul,hB.integral_eval,hB.integral_eval]
    ring
  have hv (r : ℝ≥0) : Var[canonicalBrownian r;canonicalBrownianMeasure]=(r : ℝ) := by
    rw [←covariance_self (hB.isGaussianProcess.hasGaussianLaw_eval r).aemeasurable,
      hB.covariance_eval,min_self]
  have he := variance_eq_sub hz
  simp only [Pi.sub_apply,Pi.pow_apply] at he
  rw [hmean,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at he
  rw [variance_const_mul,variance_fun_sub ht (hs.const_mul θ),variance_const_mul,
    covariance_const_mul_right,hB.covariance_eval,hv,hv] at he
  simpa only [Pi.mul_apply,Pi.sub_apply,NNReal.coe_min,mul_assoc] using he.symm


 theorem integrable_forwardBridgePoint_square (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (t : Overlap) : Integrable (fun path => forwardBridgePoint β s hs path 0 t^2)
      canonicalWienerMeasure := by
  have hm : Measurable (fun path : ForwardBridgePath => forwardBridgePoint β s hs path 0 t^2) :=
    ((continuous_forwardBridgePoint β s hs).comp
      (show Continuous (fun path : ForwardBridgePath => ((path,(0 : ℝ)),t)) by fun_prop)).pow 2 |>.measurable
  rw [canonicalWienerMeasure]
  apply (integrable_map_measure hm.aestronglyMeasurable measurable_canonicalBrownianPath.aemeasurable).mpr
  have hB := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isGaussianProcess
  have hZ := ((hB.hasGaussianLaw_eval t.1.toNNReal).memLp_two.sub
    ((hB.hasGaussianLaw_eval s.toNNReal).memLp_two.const_mul (forwardBridgeFraction s t))).const_mul β
  have hi := hZ.integrable_norm_pow'
  simpa only [Function.comp_def,forwardBridgePoint,mul_zero,zero_add,canonicalBrownianPath,
    ContinuousMap.coe_mk,Real.coe_toNNReal s hs.1.le,Pi.sub_apply,
    Real.norm_eq_abs,sq_abs] using hi

 theorem integral_forwardBridgePoint_square_le (β s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (t : Overlap) (ht : (t : ℝ) ≤ s) :
    (∫ path,forwardBridgePoint β s hs path 0 t^2 ∂canonicalWienerMeasure) ≤ β^2*s := by
  have hm : Measurable (fun path : ForwardBridgePath => forwardBridgePoint β s hs path 0 t^2) :=
    ((continuous_forwardBridgePoint β s hs).comp
      (show Continuous (fun path : ForwardBridgePath => ((path,(0 : ℝ)),t)) by fun_prop)).pow 2 |>.measurable
  rw [canonicalWienerMeasure,integral_map measurable_canonicalBrownianPath.aemeasurable hm.aestronglyMeasurable]
  simp only [forwardBridgePoint,mul_zero,zero_add,canonicalBrownianPath,
    ContinuousMap.coe_mk]
  rw [brownian_linear_combination_square]
  simp only [Real.coe_toNNReal t.1 t.2.1,Real.coe_toNNReal s hs.1.le,
    min_eq_left ht,forwardBridgeFraction,min_eq_left ((div_le_one hs.1).mpr ht)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  have he : (t : ℝ)-2*((t : ℝ)/s)*t+((t : ℝ)/s)^2*s = t-t^2/s := by
    field_simp
    ring
  rw [he]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hs.1.le) |>.trans ht

theorem forward_origin_potential_bound (β : ℝ) (μ : ParisiMeasure)
    (t : Overlap) (x : ℝ) :
    parisiPotential β μ (t,x) ≤ β^2+x^2/2 := by
  have hh := (parisiPotential_logCosh_bounds β μ t x t.property).2
  have hg := logCosh_le_square_half x
  nlinarith [t.property.1,sq_nonneg β]

theorem integrable_forward_origin_potential (β s : ℝ) (μ : ParisiMeasure)
    (hs : s ∈ Ioc (0 : ℝ) 1) (t : Overlap) :
    Integrable (fun path => parisiPotential β μ (t,forwardBridgePoint β s hs path 0 t))
      canonicalWienerMeasure := by
  have hm : Continuous (fun path : ForwardBridgePath =>
      parisiPotential β μ (t,forwardBridgePoint β s hs path 0 t)) :=
    (continuous_parisiPotential β μ).comp (continuous_const.prodMk
      ((continuous_forwardBridgePoint β s hs).comp
        (show Continuous (fun path : ForwardBridgePath => ((path,(0 : ℝ)),t)) by fun_prop)))
  apply ((integrable_const (β^2)).add
    ((integrable_forwardBridgePoint_square β s hs t).div_const 2)).mono' hm.aestronglyMeasurable
  exact .of_forall fun path => by
    rw [Real.norm_of_nonneg (parisiPotential_nonneg β μ t _ t.property.2)]
    exact forward_origin_potential_bound β μ t _

theorem integral_forward_origin_potential_le (β s : ℝ) (μ : ParisiMeasure)
    (hs : s ∈ Ioc (0 : ℝ) 1) (t : Overlap) (ht : (t : ℝ) ≤ s) :
    (∫ path,parisiPotential β μ (t,forwardBridgePoint β s hs path 0 t)
      ∂canonicalWienerMeasure) ≤ β^2+β^2*s/2 := by
  have hh := integral_mono (integrable_forward_origin_potential β s μ hs t)
    ((integrable_const (β^2)).add ((integrable_forwardBridgePoint_square β s hs t).div_const 2))
      (fun path => forward_origin_potential_bound β μ t _)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) ((integrable_forwardBridgePoint_square β s hs t).div_const 2),
    integral_const,probReal_univ,one_smul,integral_div] at hh
  exact hh.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
    (integral_forwardBridgePoint_square_le β s hs t ht) (by norm_num)))

theorem integrable_forward_origin_action_prod (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun p : Overlap×ForwardBridgePath => if (p.1 : ℝ) ≤ s then
      parisiPotential β μ (p.1,forwardBridgePoint β s hs p.2 0 p.1) else 0)
      ((μ : Measure Overlap).prod canonicalWienerMeasure) := by
  have hc : Continuous (fun p : Overlap×ForwardBridgePath =>
      parisiPotential β μ (p.1,forwardBridgePoint β s hs p.2 0 p.1)) :=
    (continuous_parisiPotential β μ).comp
      (continuous_fst.subtype_val.prodMk ((continuous_forwardBridgePoint β s hs).comp
        (show Continuous (fun p : Overlap×ForwardBridgePath => ((p.2,(0 : ℝ)),p.1)) by fun_prop)))
  have hset : MeasurableSet {p : Overlap×ForwardBridgePath | (p.1 : ℝ) ≤ s} :=
    measurableSet_le measurable_fst.subtype_val measurable_const
  have hm : Measurable (fun p : Overlap×ForwardBridgePath => if (p.1 : ℝ) ≤ s then
      parisiPotential β μ (p.1,forwardBridgePoint β s hs p.2 0 p.1) else 0) :=
    hc.measurable.ite hset measurable_const
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact .of_forall fun t => by
      by_cases ht : (t : ℝ) ≤ s
      · simpa only [ht,ite_eq_left] using integrable_forward_origin_potential β s μ hs t
      · simp only [ht,ite_false]
        exact integrable_zero _ _ _
  · apply (integrable_const (β^2+β^2*s/2)).mono'
      hm.aestronglyMeasurable.norm.integral_prod_right'
    exact .of_forall fun t => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      by_cases ht : (t : ℝ) ≤ s
      · simp only [ht,ite_eq_left]
        simp only [Real.norm_of_nonneg (parisiPotential_nonneg β μ t _ t.property.2)]
        exact integral_forward_origin_potential_le β s μ hs t ht
      · simp only [ht,ite_false,norm_zero,integral_zero]
        exact add_nonneg (sq_nonneg β)
          (div_nonneg (mul_nonneg (sq_nonneg β) hs.1.le) (by norm_num))

 theorem integrable_forwardBridgeAction_origin (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun path => forwardBridgeAction β μ s hs path 0) canonicalWienerMeasure := by
  have hi := (integrable_forward_origin_action_prod β μ s hs).integral_prod_right
  simpa only [forwardBridgeAction,forwardBridgeJet,pow_zero,one_mul,parisiSpatialField] using hi

 theorem integral_forwardBridgeAction_origin_le (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ path,forwardBridgeAction β μ s hs path 0 ∂canonicalWienerMeasure) ≤ β^2+β^2*s/2 := by
  have hf := integrable_forward_origin_action_prod β μ s hs
  have he := integral_integral_swap
    (f := fun (t : Overlap) (path : ForwardBridgePath) => if (t : ℝ) ≤ s then
      parisiPotential β μ (t,forwardBridgePoint β s hs path 0 t) else 0) hf
  simp only [forwardBridgeAction,forwardBridgeJet,pow_zero,one_mul,parisiSpatialField]
  rw [←he]
  have hh := integral_mono hf.integral_prod_left (integrable_const (β^2+β^2*s/2))
    (fun t => by
      by_cases ht : (t : ℝ) ≤ s
      · simp only [ht,ite_eq_left]
        exact integral_forward_origin_potential_le β s μ hs t ht
      · simp only [ht,ite_false,integral_zero]
        exact add_nonneg (sq_nonneg β)
          (div_nonneg (mul_nonneg (sq_nonneg β) hs.1.le) (by norm_num)))
  simpa only [integral_const,probReal_univ,one_smul] using hh

 theorem forwardBridgeCorrection_origin_bounds (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    0 ≤ forwardBridgeCorrection β μ s hs 0 ∧
      forwardBridgeCorrection β μ s hs 0 ≤ β^2+β^2*s/2 := by
  have hi := integrable_forwardBridgeAction_origin β μ s hs
  have hexp := (convexOn_exp : ConvexOn ℝ univ Real.exp).map_integral_le
    Real.continuous_exp.continuousOn isClosed_univ (.of_forall fun _ => mem_univ _) hi.neg
      (integrable_forwardBridgePathFactor β μ s hs 0)
  have hF : Real.exp (-(∫ path,forwardBridgeAction β μ s hs path 0 ∂canonicalWienerMeasure)) ≤
      forwardBridgeFactor β μ s hs 0 := by
    simpa only [Pi.neg_apply,integral_neg,forwardBridgeFactor,forwardBridgePathFactor] using hexp
  have hlog := Real.log_le_log (Real.exp_pos _) hF
  rw [Real.log_exp] at hlog
  constructor
  · unfold forwardBridgeCorrection
    exact neg_nonneg.mpr (Real.log_nonpos (forwardBridgeFactor_pos β μ s hs 0).le
      (forwardBridgeFactor_le_one β μ s hs 0))
  · unfold forwardBridgeCorrection
    have hh := integral_forwardBridgeAction_origin_le β μ s hs
    linarith

theorem forwardBridgeLeftCorrection_origin_bounds (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    0 ≤ forwardBridgeLeftCorrection β μ s hs 0 ∧
      forwardBridgeLeftCorrection β μ s hs 0 ≤ β^2+β^2*s/2 := by
  refine ⟨forwardBridgeLeftCorrection_nonneg β μ s hs 0,?_⟩
  have hh := (forwardBridgeCorrection_origin_bounds β μ s hs).2
  have ha := mul_nonneg (parisiAtomMass_nonneg μ s hs)
    (parisiPotential_nonneg β μ s 0 hs.2)
  unfold forwardBridgeLeftCorrection
  linarith

/-- Display 4.8 in the paper's rescaled clock `t = beta² s`. -/
theorem forward_correction_origin_bounds_rescaled (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) (β^2)) :
    ∃ hs : t/β^2 ∈ Ioc (0 : ℝ) 1,
      (0 ≤ forwardBridgeCorrection β μ (t/β^2) hs 0 ∧
        forwardBridgeCorrection β μ (t/β^2) hs 0 ≤ β^2+t/2) ∧
      (0 ≤ forwardBridgeLeftCorrection β μ (t/β^2) hs 0 ∧
        forwardBridgeLeftCorrection β μ (t/β^2) hs 0 ≤ β^2+t/2) := by
  have hsq : 0 < β^2 := sq_pos_of_ne_zero hβ
  have hs : t/β^2 ∈ Ioc (0 : ℝ) 1 := ⟨div_pos ht.1 hsq,(div_le_one hsq).mpr ht.2⟩
  refine ⟨hs,?_,?_⟩
  · have hh := forwardBridgeCorrection_origin_bounds β μ (t/β^2) hs
    simpa only [mul_div_cancel₀ _ hsq.ne'] using hh
  · have hh := forwardBridgeLeftCorrection_origin_bounds β μ (t/β^2) hs
    simpa only [mul_div_cancel₀ _ hsq.ne'] using hh

end FRSB
