module

public import FRSB.CrossingBridgeFields
public import FRSB.ForwardBridgeApproximation

@[expose] public section

/-! The sharp actual upper bound W_xx≤CDF, obtained from the bridge-action
 Hessian and a genuine weighted centered-square variance inequality. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB

theorem forwardBridgeJet_two_le_cdf (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeJet β μ s hs 2 path x ≤ parisiCDF μ s := by
  let S : Set Overlap := {t | (t : ℝ) ≤ s}
  have hS : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hi := (integrable_const (1 : ℝ) : Integrable (fun _ : Overlap => (1 : ℝ))
    (μ : Measure Overlap)).indicator hS
  have hb : ∀ t : Overlap,
      (if (t : ℝ) ≤ s then forwardBridgeFraction s t ^ 2 * parisiSpatialField β μ 2
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
  have hh := integral_mono (integrable_forwardBridgeJet_integrand β μ s hs 2 path x) hi hb
  rw [integral_indicator_const _ hS] at hh
  simpa only [smul_eq_mul, mul_one, Measure.real, S, parisiCDF, forwardBridgeJet] using hh

theorem hasDerivAt_forwardBridgePathFactor (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    HasDerivAt (forwardBridgePathFactor β μ s hs path)
      (-forwardBridgeJet β μ s hs 1 path x * forwardBridgePathFactor β μ s hs path x) x := by
  convert (hasDerivAt_forwardBridgeJet β μ s hs 0 path x).neg.exp using 1
  · funext y; rfl
  · dsimp [forwardBridgePathFactor, forwardBridgeAction]
    ring

theorem iteratedDeriv_forwardBridgePathFactor_one (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv 1 (forwardBridgePathFactor β μ s hs path) x =
      -forwardBridgeJet β μ s hs 1 path x * forwardBridgePathFactor β μ s hs path x := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_forwardBridgePathFactor β μ s hs path x).deriv

theorem iteratedDeriv_forwardBridgePathFactor_two (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv 2 (forwardBridgePathFactor β μ s hs path) x =
      (forwardBridgeJet β μ s hs 1 path x ^ 2 - forwardBridgeJet β μ s hs 2 path x) *
        forwardBridgePathFactor β μ s hs path x := by
  have he : deriv (forwardBridgePathFactor β μ s hs path) = fun y =>
      -forwardBridgeJet β μ s hs 1 path y * forwardBridgePathFactor β μ s hs path y :=
    funext (fun y => (hasDerivAt_forwardBridgePathFactor β μ s hs path y).deriv)
  rw [show (2 : ℕ) = 1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he]
  have hd := (hasDerivAt_forwardBridgeJet β μ s hs 1 path x).neg.mul
    (hasDerivAt_forwardBridgePathFactor β μ s hs path x)
  convert hd.deriv using 1
  dsimp only [Pi.neg_apply]
  ring

/-- Nonnegative variance proved directly by integrating a weighted
 centered square; no hidden probability-law premise is supplied. -/
theorem weighted_variance_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (w f : Ω → ℝ) (hw : ∀ sample, 0 ≤ w sample)
    (hiw : Integrable w P) (hif : Integrable (fun sample => f sample * w sample) P)
    (hif2 : Integrable (fun sample => f sample ^ 2 * w sample) P) (hp : 0 < ∫ sample, w sample ∂P) :
    0 ≤ (∫ sample, f sample ^ 2 * w sample ∂P) / (∫ sample, w sample ∂P) -
      ((∫ sample, f sample * w sample ∂P) / (∫ sample, w sample ∂P)) ^ 2 := by
  let Z := ∫ sample, w sample ∂P
  let N := ∫ sample, f sample * w sample ∂P
  let Q := ∫ sample, f sample ^ 2 * w sample ∂P
  let m := N / Z
  have he : (∫ sample, (f sample - m) ^ 2 * w sample ∂P) = Q - 2 * m * N + m ^ 2 * Z := by
    have hfun : (fun sample => (f sample - m) ^ 2 * w sample) =
        (fun sample => f sample ^ 2 * w sample - (2*m) * (f sample*w sample) + m^2 * w sample) := by
      funext sample; ring
    have ha := integral_add (hif2.sub (hif.const_mul (2*m))) (hiw.const_mul (m^2))
    have hs := integral_sub hif2 (hif.const_mul (2*m))
    simp only [Pi.sub_apply] at ha hs
    rw [hfun, ha, hs, integral_const_mul, integral_const_mul]
  have hn : 0 ≤ Q - 2*m*N + m^2*Z := by
    rw [← he]
    exact integral_nonneg (fun sample => mul_nonneg (sq_nonneg _) (hw sample))
  have hm : m * Z = N := div_mul_cancel₀ _ hp.ne'
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hp).mpr
  have heq : m * N = m^2 * Z := by rw [← hm]; ring
  nlinarith [heq]

theorem integrable_forwardBridge_weighted_jet_pow (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j n : ℕ) (x : ℝ) :
    Integrable (fun path => forwardBridgeJet β μ s hs (j+1) path x ^ n *
      forwardBridgePathFactor β μ s hs path x) canonicalWienerMeasure := by
  apply (integrable_const (uniformSpatialConstant β j ^ n)).mono'
  · have hc := (continuous_forwardBridgeJet β μ s hs (j+1)).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)
    have hf := (continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs 0).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)
    exact ((hc.pow n).mul hf).aestronglyMeasurable
  · exact .of_forall fun path => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg (forwardBridgePathFactor_pos β μ s hs path x).le]
      exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
        (norm_forwardBridgeJet_succ_le β μ s hs j path x) n)
          (forwardBridgePathFactor_le_one β μ s hs path x)
            (forwardBridgePathFactor_pos β μ s hs path x).le
            (pow_nonneg (uniformSpatialConstant_pos β j).le n)).trans_eq (mul_one _)

theorem bridge_negativeLog_second (F : ℝ → ℝ) (hc : ContDiff ℝ ∞ F)
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
theorem forwardBridgeCorrection_curvature_le_cdf (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 2 (forwardBridgeCorrection β μ s hs) x ≤ parisiCDF μ s := by
  let w : ForwardBridgePath → ℝ := fun path => forwardBridgePathFactor β μ s hs path x
  let f : ForwardBridgePath → ℝ := fun path => forwardBridgeJet β μ s hs 1 path x
  let d : ForwardBridgePath → ℝ := fun path => forwardBridgeJet β μ s hs 2 path x
  let Z := forwardBridgeFactor β μ s hs x
  let N := ∫ path, f path * w path ∂canonicalWienerMeasure
  let Q := ∫ path, f path ^ 2 * w path ∂canonicalWienerMeasure
  let S := ∫ path, d path * w path ∂canonicalWienerMeasure
  have hp : 0 < Z := forwardBridgeFactor_pos β μ s hs x
  have hiw : Integrable w canonicalWienerMeasure := integrable_forwardBridgePathFactor β μ s hs x
  have hif : Integrable (fun path => f path*w path) canonicalWienerMeasure := by
    simpa only [pow_one] using integrable_forwardBridge_weighted_jet_pow β μ s hs 0 1 x
  have hif2 : Integrable (fun path => f path^2*w path) canonicalWienerMeasure :=
    integrable_forwardBridge_weighted_jet_pow β μ s hs 0 2 x
  have hid : Integrable (fun path => d path*w path) canonicalWienerMeasure := by
    simpa only [pow_one] using integrable_forwardBridge_weighted_jet_pow β μ s hs 1 1 x
  have hvar : 0 ≤ Q/Z - (N/Z)^2 := weighted_variance_nonneg canonicalWienerMeasure w f
    (fun path => (forwardBridgePathFactor_pos β μ s hs path x).le) hiw hif hif2 hp
  have hS : S ≤ parisiCDF μ s * Z := by
    calc
      S ≤ ∫ path, parisiCDF μ s * w path ∂canonicalWienerMeasure :=
        integral_mono hid (hiw.const_mul _) (fun path =>
          mul_le_mul_of_nonneg_right (forwardBridgeJet_two_le_cdf β μ s hs path x)
            (forwardBridgePathFactor_pos β μ s hs path x).le)
      _ = _ := integral_const_mul _ _
  have hF1 : iteratedDeriv 1 (forwardBridgeFactor β μ s hs) x = -N := by
    rw [iteratedDeriv_forwardBridgeFactor]
    simp_rw [iteratedDeriv_forwardBridgePathFactor_one]
    have he : (fun path => -forwardBridgeJet β μ s hs 1 path x * w path) =
        -(fun path => f path*w path) := by funext path; simp [f]
    rw [he]
    change (∫ path, -(f path*w path) ∂canonicalWienerMeasure) = -N
    rw [integral_neg]
  have hF2 : iteratedDeriv 2 (forwardBridgeFactor β μ s hs) x = Q-S := by
    rw [iteratedDeriv_forwardBridgeFactor]
    simp_rw [iteratedDeriv_forwardBridgePathFactor_two]
    have he : (fun path => (forwardBridgeJet β μ s hs 1 path x ^ 2 -
        forwardBridgeJet β μ s hs 2 path x) * w path) =
        (fun path => f path^2*w path) - (fun path => d path*w path) := by
      funext path; dsimp [f, d]; ring
    rw [he]
    change (∫ path, f path^2*w path - d path*w path ∂canonicalWienerMeasure) = Q-S
    rw [integral_sub hif2 hid]
  have hW := bridge_negativeLog_second (forwardBridgeFactor β μ s hs)
    (contDiff_forwardBridgeFactor β μ s hs) (forwardBridgeFactor_pos β μ s hs) x
  change iteratedDeriv 2 (forwardBridgeCorrection β μ s hs) x = _ at hW
  rw [hF1, hF2] at hW
  have he : -(Q-S)/Z + (-N)^2/Z^2 = S/Z - (Q/Z - (N/Z)^2) := by
    field_simp [hp.ne']; ring
  rw [he] at hW
  have hh : S/Z ≤ parisiCDF μ s := (div_le_iff₀ hp).mpr hS
  rw [hW]
  linarith

end FRSB
