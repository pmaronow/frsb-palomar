module

public import FRSB.CrossMagnetizationDensity

@[expose] public section

/-! Genuine fixed-magnetization time differentiation and the weighted law
from Remark 5.3, with explicit conversion between physical overlap time and
Section 5's clock. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB

 theorem backwardTime_physicalClock (β : ℝ) (hβ : β ≠ 0) (s : ℝ) :
    backwardTime β (β^2*(1-s)) = s := by
  unfold backwardTime
  field_simp
  ring

 theorem hasDerivAt_magnetizationInverse_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => magnetizationInverse β μ t v)
      (β^2 * actualCrossingVelocity β μ m (s,magnetizationInverse β μ s v)) s := by
  have hτ : backwardTime β (β^2*(1-s)) ∈ Ioo a b := by
    rwa [backwardTime_physicalClock β hβ]
  have hd := (hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc hτ hv).comp s
    (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).const_mul (β^2))
  have he : (fun t => backwardMagnetizationInverse β μ (β^2*(1-t)) v) =
      fun t => magnetizationInverse β μ t v := by
    funext t
    simp only [backwardMagnetizationInverse,backwardTime_physicalClock β hβ]
  simp only [Function.comp_def,Pi.sub_apply,id_eq] at hd
  rw [show (fun t => backwardMagnetizationInverse β μ (β^2*(1-t)) v) =
    (fun t => magnetizationInverse β μ t v) from he] at hd
  have hB : backwardB β μ (s,magnetizationInverse β μ s v) = v := by
    rw [backwardB_eq_gradient β μ s _ ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩]
    exact parisiGradient_magnetizationInverse β hβ μ s v ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩ hv
  convert hd using 1
  · dsimp only [backwardTauZ,backwardTauD,backwardMagnetizationInverse]
    rw [backwardTime_physicalClock β hβ]
    dsimp only [actualCrossingVelocity]
    rw [hB]
    dsimp only [backwardZ,backwardC]
    ring

 theorem hasDerivAt_magnetization_coordinate_comp (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1)
    (F : ℝ×ℝ → ℝ) (FT FX : ℝ)
    (hF : HasFDerivAt F ((ContinuousLinearMap.toSpanSingleton ℝ FT).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ FX)) (s,magnetizationInverse β μ s v)) :
    HasDerivAt (fun t => F (t,magnetizationInverse β μ t v))
      (FT + β^2*actualCrossingVelocity β μ m (s,magnetizationInverse β μ s v)*FX) s := by
  have hd := hF.comp_hasDerivAt s ((hasDerivAt_id s).prodMk
    (hasDerivAt_magnetizationInverse_time β hβ μ ha hab hb hc hs hv))
  convert hd using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,one_mul]

 def magnetizationR (β : ℝ) (μ : ParisiMeasure) (s v : ℝ) : ℝ :=
  parisiForwardDensity β μ s (magnetizationInverse β μ s v) *
    backwardC β μ (s,magnetizationInverse β μ s v)

 theorem magnetizationR_eq_weightedDensity (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (v : ℝ) :
    magnetizationR β μ s v = magnetizationWeightedDensity β μ s hs v := by
  simp only [magnetizationR,magnetizationWeightedDensity,parisiForwardDensity_eq β μ hs]

 theorem magnetizationR_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (v : ℝ) : 0 < magnetizationR β μ s v := by
  rw [magnetizationR_eq_weightedDensity β μ s hs]
  exact mul_pos (forwardBridgeDensity_pos β hβ μ s hs _)
    (backwardC_pos β hβ μ s _ ⟨hs.1.le,hs.2⟩)

 theorem hasDerivAt_magnetizationR_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (magnetizationR β μ s)
      (-(bridgeCrossingN β μ s hs (magnetizationInverse β μ s v) +
        backwardZ β μ (s,magnetizationInverse β μ s v)) *
          forwardBridgeDensity β μ s hs (magnetizationInverse β μ s v)) v := by
  let x := magnetizationInverse β μ s v
  have hi := hasDerivAt_magnetizationInverse β hβ μ s v ⟨hs.1.le,hs.2⟩ hv
  have hp := (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x).comp v hi
  have hC := (hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le,hs.2⟩).comp v hi
  have hd := hp.mul hC
  simp only [Function.comp_def] at hd
  convert hd using 1
  · funext y
    simp only [magnetizationR,parisiForwardDensity_eq β μ hs,backwardC]
    rfl
  · rw [backwardD_three_eq_neg_two_C_z β hβ μ s x ⟨hs.1.le,hs.2⟩,
      ← backwardC_eq_hessian β μ s x ⟨hs.1.le,hs.2⟩]
    have hn := (backwardC_pos β hβ μ s x ⟨hs.1.le,hs.2⟩).ne'
    dsimp only [x,bridgeCrossingN,backwardC] at *
    field_simp
    ring

 theorem magnetizationR_log_score (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    bridgeCrossingN β μ s hs (magnetizationInverse β μ s v) +
      backwardZ β μ (s,magnetizationInverse β μ s v) =
        -backwardC β μ (s,magnetizationInverse β μ s v) *
          deriv (fun b => Real.log (magnetizationR β μ s b)) v := by
  rw [((hasDerivAt_magnetizationR_spatial β hβ μ s hs hv).log
    (magnetizationR_pos β hβ μ s hs v).ne').deriv,magnetizationR_eq_weightedDensity β μ s hs]
  have hp := (forwardBridgeDensity_pos β hβ μ s hs (magnetizationInverse β μ s v)).ne'
  have hC := (backwardC_pos β hβ μ s (magnetizationInverse β μ s v) ⟨hs.1.le,hs.2⟩).ne'
  dsimp only [magnetizationWeightedDensity]
  field_simp

 theorem hasStrictFDerivAt_parisiForwardDensity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s x : ℝ} (hs : s ∈ Ioo a b) :
    HasStrictFDerivAt (fun p : ℝ×ℝ => parisiForwardDensity β μ p.1 p.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (parisiForwardDensityT β μ m s x)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv (parisiForwardDensity β μ s) x))) (s,x) := by
  have hnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (s,x),p.1 ∈ Ioo a b :=
    continuous_fst.continuousAt.eventually (isOpen_Ioo.mem_nhds hs)
  have hN : Ioo a b ×ˢ (univ : Set ℝ) ∈ 𝓝 (s,x) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs,mem_univ _⟩
  have hfields := continuousOn_parisiForwardDensity_fields β hβ μ ha hab hb hc
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun t y => parisiForwardDensity β μ t y) (u := (s,x))
    (f₁ := fun t y => ContinuousLinearMap.toSpanSingleton ℝ (parisiForwardDensityT β μ m t y))
    (f₂ := fun t y => ContinuousLinearMap.toSpanSingleton ℝ (deriv (parisiForwardDensity β μ t) y))
  · filter_upwards [hnear] with p hp
    exact (hasDerivAt_parisiForwardDensity_T β hβ μ ha hab hb hc hp p.2).hasFDerivAt
  · filter_upwards [hnear] with p hp
    have ht : p.1 ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hp.1,hp.2.le.trans hb⟩
    change HasFDerivAt (parisiForwardDensity β μ p.1)
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv (parisiForwardDensity β μ p.1) p.2)) p.2
    rw [parisiForwardDensity_eq β μ ht]
    exact ((contDiff_forwardBridgeDensity β μ p.1 ht).differentiable (by simp) p.2).hasDerivAt.hasFDerivAt
  · exact (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuousAt.comp
      (hfields.2.2.2.continuousAt hN)
  · exact (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuousAt.comp
      (hfields.2.1.continuousAt hN)

 theorem hasDerivAt_magnetizationCurvature_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => backwardC β μ (t,magnetizationInverse β μ t v))
      (β^2*backwardQ β μ m (s,magnetizationInverse β μ s v)*
        backwardC β μ (s,magnetizationInverse β μ s v)) s := by
  have hτ : backwardTime β (β^2*(1-s)) ∈ Ioo a b := by
    rwa [backwardTime_physicalClock β hβ]
  have hd := (hasDerivAt_backwardChi_time β hβ μ ha hab hb hc hτ hv).comp s
    (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).const_mul (β^2))
  have he : (fun t => backwardChi β μ (β^2*(1-t)) v) =
      fun t => backwardC β μ (t,magnetizationInverse β μ t v) := by
    funext t
    simp only [backwardChi,backwardTauD,backwardMagnetizationInverse,
      backwardTime_physicalClock β hβ,backwardC]
  simp only [Function.comp_def,Pi.sub_apply,id_eq] at hd
  rw [he] at hd
  convert hd using 1
  dsimp only [backwardTauQ,backwardChi,backwardTauD,backwardMagnetizationInverse]
  rw [backwardTime_physicalClock β hβ]
  dsimp only [backwardQ,backwardC]
  ring

 theorem hasDerivAt_magnetizationForwardDensity_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => parisiForwardDensity β μ t (magnetizationInverse β μ t v))
      (β^2*(bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
        (magnetizationInverse β μ s v)/2-backwardZ β μ (s,magnetizationInverse β μ s v)^2-
          m*backwardC β μ (s,magnetizationInverse β μ s v))*
            parisiForwardDensity β μ s (magnetizationInverse β μ s v)) s := by
  let ht : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
  let x := magnetizationInverse β μ s v
  have hd := hasDerivAt_magnetization_coordinate_comp β hβ μ ha hab hb hc hs hv
    (fun p : ℝ×ℝ => parisiForwardDensity β μ p.1 p.2)
    (parisiForwardDensityT β μ m s x) (deriv (parisiForwardDensity β μ s) x)
    (hasStrictFDerivAt_parisiForwardDensity β hβ μ ha hab hb hc hs).hasFDerivAt
  have hm : parisiCDF μ s = m := hc s ⟨hs.1.le,hs.2⟩
  have hp := hasDerivAt_forwardBridgeDensity_score β hβ μ s ht x
  rw [← parisiForwardDensity_eq β μ ht] at hp
  convert hd using 1
  rw [hp.deriv,← hm,parisiForwardDensityT_eq_crossing_score β hβ μ s ht x,
    parisiForwardDensity_eq β μ ht]
  dsimp [actualCrossingVelocity,bridgeCrossingN,x]
  ring

 theorem hasDerivAt_magnetizationR_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => magnetizationR β μ t v)
      (β^2*(bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
        (magnetizationInverse β μ s v)/2-backwardQ β μ m (s,magnetizationInverse β μ s v)-
          backwardH β μ m (s,magnetizationInverse β μ s v))*magnetizationR β μ s v) s := by
  have hd := (hasDerivAt_magnetizationForwardDensity_time β hβ μ ha hab hb hc hs hv).mul
    (hasDerivAt_magnetizationCurvature_time β hβ μ ha hab hb hc hs hv)
  convert hd using 1
  · rfl
  · rw [backwardH_eq_z_sq_mC_sub_twoQ]
    dsimp [magnetizationR]
    ring

 theorem magnetizationR_log_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun t => Real.log (magnetizationR β μ t v)) s =
      β^2*(bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
        (magnetizationInverse β μ s v)/2-backwardQ β μ m (s,magnetizationInverse β μ s v)-
          backwardH β μ m (s,magnetizationInverse β μ s v)) := by
  let ht : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
  rw [((hasDerivAt_magnetizationR_time β hβ μ ha hab hb hc hs hv).log
    (magnetizationR_pos β hβ μ s ht v).ne').deriv]
  exact mul_div_cancel_right₀ _ (magnetizationR_pos β hβ μ s ht v).ne'

 theorem hasDerivAt_deriv_magnetizationR_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (magnetizationR β μ s))
      ((bridgeCrossingN β μ s hs (magnetizationInverse β μ s v)^2-
        backwardZ β μ (s,magnetizationInverse β μ s v)^2-
          bridgeCrossingVxx β μ s hs (magnetizationInverse β μ s v)-
          backwardQ β μ (parisiCDF μ s) (s,magnetizationInverse β μ s v)-
          backwardZx β μ (s,magnetizationInverse β μ s v))*
        forwardBridgeDensity β μ s hs (magnetizationInverse β μ s v)/
          backwardC β μ (s,magnetizationInverse β μ s v)) v := by
  let x := magnetizationInverse β μ s v
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hi := hasDerivAt_magnetizationInverse β hβ μ s v ht hv
  rw [← backwardC_eq_hessian β μ s x ht] at hi
  have hn := (hasDerivAt_bridgeCrossingN β hβ μ s hs x).comp v hi
  have hz := (hasDerivAt_backwardZ β hβ μ s x ht).comp v hi
  have hp := (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x).comp v hi
  have hd := (hn.add hz).neg.mul hp
  have he : deriv (magnetizationR β μ s) =ᶠ[𝓝 v]
      (fun b => -(bridgeCrossingN β μ s hs (magnetizationInverse β μ s b)+
        backwardZ β μ (s,magnetizationInverse β μ s b))*
          forwardBridgeDensity β μ s hs (magnetizationInverse β μ s b)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with b hb
    exact (hasDerivAt_magnetizationR_spatial β hβ μ s hs hb).deriv
  simp only [Function.comp_def] at hd
  convert hd.congr_of_eventuallyEq he using 1
  have hC := (backwardC_pos β hβ μ s x ht).ne'
  dsimp only [x,bridgeCrossingN,Pi.neg_apply,Pi.add_apply] at *
  field_simp
  ring

 theorem magnetizationR_second_spatial_rate (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    backwardC β μ (s,magnetizationInverse β μ s v)^2 *
      deriv (deriv (magnetizationR β μ s)) v / (2*magnetizationR β μ s v) =
        bridgeCrossingK β μ s hs (magnetizationInverse β μ s v)/2-
          3*backwardQ β μ (parisiCDF μ s) (s,magnetizationInverse β μ s v)-
          backwardH β μ (parisiCDF μ s) (s,magnetizationInverse β μ s v) := by
  rw [(hasDerivAt_deriv_magnetizationR_spatial β hβ μ s hs hv).deriv,
    backwardH_eq_z_sq_mC_sub_twoQ,magnetizationR_eq_weightedDensity β μ s hs]
  have hp := (forwardBridgeDensity_pos β hβ μ s hs (magnetizationInverse β μ s v)).ne'
  have hC := (backwardC_pos β hβ μ s (magnetizationInverse β μ s v) ⟨hs.1.le,hs.2⟩).ne'
  dsimp only [magnetizationWeightedDensity,bridgeCrossingK,crossingK,backwardQ,
    backwardQJet,backwardZx]
  field_simp
  ring

 theorem magnetizationR_weighted_law (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ t ∈ Ico a b,parisiCDF μ t = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun t => magnetizationR β μ t v) s = β^2 *
      (backwardC β μ (s,magnetizationInverse β μ s v)^2 *
        deriv (deriv (magnetizationR β μ s)) v / 2+
        2*backwardQ β μ m (s,magnetizationInverse β μ s v)*magnetizationR β μ s v) := by
  let ht : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
  have hm : parisiCDF μ s = m := hc s ⟨hs.1.le,hs.2⟩
  have hr := magnetizationR_second_spatial_rate β hβ μ s ht hv
  have hR := (magnetizationR_pos β hβ μ s ht v).ne'
  rw [hm] at hr
  rw [(hasDerivAt_magnetizationR_time β hβ μ ha hab hb hc hs hv).deriv]
  rw [mul_assoc (β^2)]
  apply congrArg (fun z : ℝ => β^2*z)
  have hh := (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hR)).mp hr
  nlinarith [hh]

 theorem magnetizationR_centered_identity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    -deriv (fun b => backwardC β μ (s,magnetizationInverse β μ s b)*
      backwardZ β μ (s,magnetizationInverse β μ s b)*magnetizationR β μ s b) v /
        magnetizationR β μ s v =
      actualCrossingPhi β μ (parisiCDF μ s) (s,magnetizationInverse β μ s v)+
        bridgeCrossingPsi β μ s hs (magnetizationInverse β μ s v) := by
  let x := magnetizationInverse β μ s v
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hi := hasDerivAt_magnetizationInverse β hβ μ s v ht hv
  rw [← backwardC_eq_hessian β μ s x ht] at hi
  have hC := (hasDerivAt_backwardD β μ 2 s x ht).comp v hi
  have hz := (hasDerivAt_backwardZ β hβ μ s x ht).comp v hi
  have hr := hasDerivAt_magnetizationR_spatial β hβ μ s hs hv
  have hd := (hC.mul hz).mul hr
  have hfun : (fun b => backwardC β μ (s,magnetizationInverse β μ s b)*
      backwardZ β μ (s,magnetizationInverse β μ s b)*magnetizationR β μ s b) =
      (((fun y => backwardD β μ 2 (s,y)) ∘ magnetizationInverse β μ s)*
        ((fun y => backwardZ β μ (s,y)) ∘ magnetizationInverse β μ s))*magnetizationR β μ s := rfl
  rw [hfun,hd.deriv,backwardD_three_eq_neg_two_C_z β hβ μ s x ht,
    magnetizationR_eq_weightedDensity β μ s hs]
  have hp := (forwardBridgeDensity_pos β hβ μ s hs x).ne'
  have hCp := (backwardC_pos β hβ μ s x ht).ne'
  dsimp only [Function.comp_def,Pi.mul_apply,actualCrossingPhi,crossingPhi,
    bridgeCrossingPsi,magnetizationWeightedDensity,x,backwardQ,backwardQJet,backwardZx,backwardC] at *
  field_simp
  ring

end FRSB
