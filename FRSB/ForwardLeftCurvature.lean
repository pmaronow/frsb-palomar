module

public import FRSB.CrossingBridgeCurvature
public import FRSB.ForwardLeftJets

@[expose] public section

/-! The sharp actual upper bound W_xx≤CDF, obtained from the bridge-action
 Hessian and a genuine weighted centered-square variance inequality. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB

theorem forwardBridgeLeftJet_two_le_leftMass (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeLeftJet β μ s hs 2 path x ≤ parisiLeftMass μ s := by
  let S : Set Overlap := {t | (t : ℝ) < s}
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have hi := (integrable_const (1 : ℝ) : Integrable (fun _ : Overlap => (1 : ℝ))
    (μ : Measure Overlap)).indicator hS
  have hb : ∀ t : Overlap,
      (if (t : ℝ) < s then forwardBridgeFraction s t ^ 2 * parisiSpatialField β μ 2
        (t, forwardBridgePoint β s hs path x t) else 0) ≤ S.indicator (fun _ => (1 : ℝ)) t := by
    intro t
    simp only [Set.indicator_apply, S, mem_ofPred_eq]
    split_ifs
    · have hC : parisiSpatialField β μ 2 (t, forwardBridgePoint β s hs path x t) ≤ 1 := by
        change backwardC β μ (t, forwardBridgePoint β s hs path x t) ≤ 1
        rw [backwardC_eq_hessian β μ t _ t.property]
        exact parisiHessian_le_one_all β μ _
      exact (mul_le_mul_of_nonneg_left hC (sq_nonneg _)).trans
        (by simpa only [mul_one] using
          (pow_le_one₀ (forwardBridgeFraction_mem s hs.1 t).1
            (forwardBridgeFraction_mem s hs.1 t).2 : forwardBridgeFraction s t ^ 2 ≤ 1))
    · exact le_rfl
  have hh := integral_mono (integrable_forwardBridgeLeftJet_integrand β μ s hs 2 path x) hi hb
  rw [integral_indicator_const _ hS] at hh
  simpa only [smul_eq_mul, mul_one, Measure.real, S, parisiLeftMass, forwardBridgeLeftJet] using hh

theorem hasDerivAt_forwardBridgeLeftPathFactor (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    HasDerivAt (forwardBridgeLeftPathFactor β μ s hs path)
      (-forwardBridgeLeftJet β μ s hs 1 path x * forwardBridgeLeftPathFactor β μ s hs path x) x := by
  have he : forwardBridgeLeftAction β μ s hs path = forwardBridgeLeftJet β μ s hs 0 path := by
    funext y
    simp only [forwardBridgeLeftAction, forwardBridgeLeftJet, pow_zero, one_mul, parisiSpatialField]
  have hd : HasDerivAt (forwardBridgeLeftAction β μ s hs path)
      (forwardBridgeLeftJet β μ s hs 1 path x) x := by
    rw [he]
    exact hasDerivAt_forwardBridgeLeftJet β μ s hs 0 path x
  convert hd.neg.exp using 1
  · rfl
  · dsimp [forwardBridgeLeftPathFactor]
    ring

theorem iteratedDeriv_forwardBridgeLeftPathFactor_one (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv 1 (forwardBridgeLeftPathFactor β μ s hs path) x =
      -forwardBridgeLeftJet β μ s hs 1 path x * forwardBridgeLeftPathFactor β μ s hs path x := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_forwardBridgeLeftPathFactor β μ s hs path x).deriv

theorem iteratedDeriv_forwardBridgeLeftPathFactor_two (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv 2 (forwardBridgeLeftPathFactor β μ s hs path) x =
      (forwardBridgeLeftJet β μ s hs 1 path x ^ 2 - forwardBridgeLeftJet β μ s hs 2 path x) *
        forwardBridgeLeftPathFactor β μ s hs path x := by
  have he : deriv (forwardBridgeLeftPathFactor β μ s hs path) = fun y =>
      -forwardBridgeLeftJet β μ s hs 1 path y * forwardBridgeLeftPathFactor β μ s hs path y :=
    funext (fun y => (hasDerivAt_forwardBridgeLeftPathFactor β μ s hs path y).deriv)
  rw [show (2 : ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he]
  have hd := (hasDerivAt_forwardBridgeLeftJet β μ s hs 1 path x).neg.mul
    (hasDerivAt_forwardBridgeLeftPathFactor β μ s hs path x)
  convert hd.deriv using 1
  dsimp only [Pi.neg_apply]
  ring

theorem integrable_forwardBridgeLeft_weighted_jet_pow (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j n : ℕ) (x : ℝ) :
    Integrable (fun path => forwardBridgeLeftJet β μ s hs (j+1) path x ^ n *
      forwardBridgeLeftPathFactor β μ s hs path x) canonicalWienerMeasure := by
  apply (integrable_const (uniformSpatialConstant β j ^ n)).mono'
  · have hc := (continuous_forwardBridgeLeftJet β μ s hs (j+1)).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)
    have hf := (continuous_iteratedDeriv_forwardBridgeLeftPathFactor β μ s hs 0).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)
    exact ((hc.pow n).mul hf).aestronglyMeasurable
  · exact .of_forall fun path => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg (forwardBridgeLeftPathFactor_pos β μ s hs path x).le]
      exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
        (norm_forwardBridgeLeftJet_succ_le β μ s hs j path x) n)
          (forwardBridgeLeftPathFactor_le_one β μ s hs path x)
            (forwardBridgeLeftPathFactor_pos β μ s hs path x).le
            (pow_nonneg (uniformSpatialConstant_pos β j).le n)).trans_eq (mul_one _)

theorem bridgeLeft_negativeLog_second (F : ℝ → ℝ) (hc : ContDiff ℝ ∞ F)
    (hp : ∀ x, 0 < F x) (x : ℝ) :
    iteratedDeriv 2 (fun y => -Real.log (F y)) x =
      -iteratedDeriv 2 F x / F x + iteratedDeriv 1 F x ^ 2 / F x ^ 2 := by
  have hone : iteratedDeriv 1 (fun y => -Real.log (F y)) x = -iteratedDeriv 1 F x / F x := by
    have hfun : (-(fun y => Real.log (F y))) = fun y => -Real.log (F y) := rfl
    have hh := ((hc.differentiable (by simp) x).hasDerivAt.log (hp x).ne').neg.deriv
    rw [hfun] at hh
    simpa only [iteratedDeriv_one, neg_div] using hh
  have h := iteratedDeriv_negativeLog_formula F hc hp 1 x
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul, zero_add, Nat.sub_zero, Nat.reduceAdd] at h
  rw [hone] at h
  rw [h]
  field_simp [(hp x).ne']
  ring

/-- The sharp forward upper curvature bound, instantiated with the
 actual arbitrary-measure Parisi potential and concrete Wiener bridge. -/
theorem forwardBridgeLeftCorrection_curvature_le_leftMass (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 2 (forwardBridgeLeftCorrection β μ s hs) x ≤ parisiLeftMass μ s := by
  let w : ForwardBridgePath → ℝ := fun path => forwardBridgeLeftPathFactor β μ s hs path x
  let f : ForwardBridgePath → ℝ := fun path => forwardBridgeLeftJet β μ s hs 1 path x
  let d : ForwardBridgePath → ℝ := fun path => forwardBridgeLeftJet β μ s hs 2 path x
  let Z := forwardBridgeLeftFactor β μ s hs x
  let N := ∫ path, f path * w path ∂canonicalWienerMeasure
  let Q := ∫ path, f path ^ 2 * w path ∂canonicalWienerMeasure
  let S := ∫ path, d path * w path ∂canonicalWienerMeasure
  have hp : 0 < Z := forwardBridgeLeftFactor_pos β μ s hs x
  have hiw : Integrable w canonicalWienerMeasure := integrable_forwardBridgeLeftPathFactor β μ s hs x
  have hif : Integrable (fun path => f path*w path) canonicalWienerMeasure := by
    simpa only [pow_one] using integrable_forwardBridgeLeft_weighted_jet_pow β μ s hs 0 1 x
  have hif2 : Integrable (fun path => f path^2*w path) canonicalWienerMeasure :=
    integrable_forwardBridgeLeft_weighted_jet_pow β μ s hs 0 2 x
  have hid : Integrable (fun path => d path*w path) canonicalWienerMeasure := by
    simpa only [pow_one] using integrable_forwardBridgeLeft_weighted_jet_pow β μ s hs 1 1 x
  have hZ : Z = ∫ path, w path ∂canonicalWienerMeasure :=
    forwardBridgeLeftFactor_eq_integral β μ s hs x
  have hvar := weighted_variance_nonneg canonicalWienerMeasure w f
    (fun path => (forwardBridgeLeftPathFactor_pos β μ s hs path x).le) hiw hif hif2 (by rw [← hZ]; exact hp)
  rw [← hZ] at hvar
  have hS : S ≤ parisiLeftMass μ s * Z := by
    calc
      S ≤ ∫ path, parisiLeftMass μ s * w path ∂canonicalWienerMeasure :=
        integral_mono hid (hiw.const_mul _) (fun path =>
          mul_le_mul_of_nonneg_right (forwardBridgeLeftJet_two_le_leftMass β μ s hs path x)
            (forwardBridgeLeftPathFactor_pos β μ s hs path x).le)
      _ = _ := by rw [integral_const_mul, ← hZ]
  have hF1 : iteratedDeriv 1 (forwardBridgeLeftFactor β μ s hs) x = -N := by
    rw [iteratedDeriv_forwardBridgeLeftFactor]
    simp_rw [iteratedDeriv_forwardBridgeLeftPathFactor_one]
    have he : (fun path => -forwardBridgeLeftJet β μ s hs 1 path x * w path) =
        -(fun path => f path*w path) := by funext path; simp [f]
    rw [he]
    change (∫ path, -(f path*w path) ∂canonicalWienerMeasure) = -N
    rw [integral_neg]
  have hF2 : iteratedDeriv 2 (forwardBridgeLeftFactor β μ s hs) x = Q-S := by
    rw [iteratedDeriv_forwardBridgeLeftFactor]
    simp_rw [iteratedDeriv_forwardBridgeLeftPathFactor_two]
    have he : (fun path => (forwardBridgeLeftJet β μ s hs 1 path x ^ 2 -
        forwardBridgeLeftJet β μ s hs 2 path x) * w path) =
        (fun path => f path^2*w path) - (fun path => d path*w path) := by
      funext path; dsimp [f, d]; ring
    rw [he]
    change (∫ path, f path^2*w path - d path*w path ∂canonicalWienerMeasure) = Q-S
    rw [integral_sub hif2 hid]
  have hW := bridgeLeft_negativeLog_second (forwardBridgeLeftFactor β μ s hs)
    (contDiff_forwardBridgeLeftFactor β μ s hs) (forwardBridgeLeftFactor_pos β μ s hs) x
  have hfun : (fun y => -Real.log (forwardBridgeLeftFactor β μ s hs y)) =
      forwardBridgeLeftCorrection β μ s hs := by
    funext y
    exact (forwardBridgeLeftCorrection_eq_negativeLog β μ s hs y).symm
  rw [hfun] at hW
  rw [hF1, hF2] at hW
  have he : -(Q-S)/Z + (-N)^2/Z^2 = S/Z - (Q/Z - (N/Z)^2) := by
    field_simp [hp.ne']; ring
  rw [he] at hW
  have hh : S/Z ≤ parisiLeftMass μ s := (div_le_iff₀ hp).mpr hS
  rw [hW]
  linarith

end FRSB
