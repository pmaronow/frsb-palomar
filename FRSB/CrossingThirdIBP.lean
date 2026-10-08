module

public import FRSB.CrossingThirdFlux
public import FRSB.CrossingBridgeProducts

@[expose] public section

/-! Genuine spatial integration by parts connecting the actual third Gamma
source to its positive covariance representation. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

theorem integrable_weighted_of_crossingWeightLaw (w f : ℝ → ℝ)
    (hw : IntegrableOn w (Ioi (0 : ℝ))) (hp : ∀ x > 0,0 < w x)
    (hf : Integrable f (crossingWeightLaw w)) :
    IntegrableOn (fun x => f x * w x) (Ioi (0 : ℝ)) := by
  have hm := (hw.aestronglyMeasurable.aemeasurable.div_const (crossingWeightMass w)).ennreal_ofReal
  have hZ := crossingWeightMass_pos w hw hp
  have hi := ((integrable_withDensity_iff_integrable_smul₀' hm
    (.of_forall fun x => ENNReal.ofReal_lt_top)).mp hf).const_mul (crossingWeightMass w)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change crossingWeightMass w * ((ENNReal.ofReal (w x / crossingWeightMass w)).toReal * f x) = _
  rw [ENNReal.toReal_ofReal (div_pos (hp x hx) hZ).le]
  field_simp

theorem norm_bridgeCrossingThirdSource_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖bridgeCrossingThirdSource β μ s x‖ ≤ 59 := by
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hmC : ‖parisiCDF μ s * backwardC β μ (s,x)‖ ≤ 1 := by
    rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s),
      Real.norm_of_nonneg (backwardC_pos β hβ μ s x hs).le]
    exact (mul_le_mul (parisiCDF_le_one μ s) (backwardC_le_one β hβ μ s x hs)
      (backwardC_pos β hβ μ s x hs).le zero_le_one).trans_eq (mul_one _)
  have hPhiQ : ‖actualCrossingPhi β μ (parisiCDF μ s) (s,x) -
      backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 4 := by
    apply (norm_sub_le _ _).trans
    have hq : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x hs
    linarith [norm_actualCrossingPhi_le_three β hβ μ s x hs]
  have hPhiQsq : ‖actualCrossingPhi β μ (parisiCDF μ s) (s,x) -
      backwardQ β μ (parisiCDF μ s) (s,x)‖ ^ 2 ≤ 16 := by
    nlinarith [norm_nonneg (actualCrossingPhi β μ (parisiCDF μ s) (s,x) -
      backwardQ β μ (parisiCDF μ s) (s,x))]
  have hzsq : ‖backwardZ β μ (s,x)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hmCsq : ‖parisiCDF μ s * backwardC β μ (s,x)‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hmC
  have hform : bridgeCrossingThirdSource β μ s x =
      2 * (actualCrossingPhi β μ (parisiCDF μ s) (s,x) -
        backwardQ β μ (parisiCDF μ s) (s,x)) ^ 2 -
      24 * (parisiCDF μ s * backwardC β μ (s,x)) * backwardZ β μ (s,x) ^ 2 +
      3 * (parisiCDF μ s * backwardC β μ (s,x)) ^ 2 := by
    unfold bridgeCrossingThirdSource crossingThirdSource actualCrossingPhi
    ring
  rw [hform]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  simp only [norm_mul,norm_pow,show ‖(2 : ℝ)‖ = 2 by norm_num,
    show ‖(24 : ℝ)‖ = 24 by norm_num,show ‖(3 : ℝ)‖ = 3 by norm_num]
  have hprod : ‖parisiCDF μ s * backwardC β μ (s,x)‖ *
      ‖backwardZ β μ (s,x)‖ ^ 2 ≤ 1 :=
    (mul_le_mul hmC hzsq (by positivity) zero_le_one).trans_eq (mul_one _)
  simp only [norm_mul] at hmCsq hprod
  nlinarith

theorem continuous_bridgeCrossingThirdSource (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : Continuous (bridgeCrossingThirdSource β μ s) := by
  have hC : Continuous (fun x => backwardC β μ (s,x)) :=
    (contDiff_backwardD_spatial β μ s hs 2).continuous
  have hz : Continuous (fun x => backwardZ β μ (s,x)) :=
    (backward_fields_smooth β hβ μ (parisiCDF μ s) s hs).1.continuous
  have hQ : Continuous (fun x => backwardQ β μ (parisiCDF μ s) (s,x)) :=
    (backward_fields_smooth β hβ μ (parisiCDF μ s) s hs).2.2.2.1.continuous
  unfold bridgeCrossingThirdSource crossingThirdSource crossingPhi
  have hh : Continuous (fun x => 2 * ((2 * backwardZ β μ (s,x) ^ 2 -
      parisiCDF μ s * backwardC β μ (s,x)) - backwardQ β μ (parisiCDF μ s) (s,x)) ^ 2 -
      24 * parisiCDF μ s * backwardC β μ (s,x) * backwardZ β μ (s,x) ^ 2 +
      3 * parisiCDF μ s ^ 2 * backwardC β μ (s,x) ^ 2) := by
    fun_prop
  exact hh

theorem integrable_bridgeCrossingThirdSource (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (bridgeCrossingThirdSource β μ s)
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  let := bridgeCrossingWeightLaw_isProbability β hβ μ s hs
  apply (integrable_const (59 : ℝ)).mono'
    (continuous_bridgeCrossingThirdSource β hβ μ s ⟨hs.1.le,hs.2⟩).aestronglyMeasurable
  exact .of_forall fun x => norm_bridgeCrossingThirdSource_le β hβ μ s x ⟨hs.1.le,hs.2⟩

theorem norm_bridgeCrossingThirdFlux_linear (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖bridgeCrossingThirdFlux β μ s hs x‖ ≤ (3/2 : ℝ) * |x| / (β ^ 2*s) + 12 := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x ht
  have hz3 : ‖backwardZ β μ (s,x)‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have hmC : ‖parisiCDF μ s * backwardC β μ (s,x)‖ ≤ 1 := by
    rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s),
      Real.norm_of_nonneg (backwardC_pos β hβ μ s x ht).le]
    exact (mul_le_mul (parisiCDF_le_one μ s) (backwardC_le_one β hβ μ s x ht)
      (backwardC_pos β hβ μ s x ht).le zero_le_one).trans_eq (mul_one _)
  have hPhiN : ‖actualCrossingPhi β μ (parisiCDF μ s) (s,x) * bridgeCrossingN β μ s hs x‖ ≤
      3 * (|x|/(β^2*s)+3) := by
    rw [norm_mul]
    exact mul_le_mul (norm_actualCrossingPhi_le_three β hβ μ s x ht)
      (norm_bridgeCrossingN_linear β hβ μ s hs x) (norm_nonneg _) (by norm_num)
  have hprod : ‖(parisiCDF μ s * backwardC β μ (s,x)) * backwardZ β μ (s,x)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul hmC hz (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
  have he : bridgeCrossingThirdFlux β μ s hs x =
      (actualCrossingPhi β μ (parisiCDF μ s) (s,x) * bridgeCrossingN β μ s hs x) / 2 -
      2 * backwardZ β μ (s,x) ^ 3 + (11/2 : ℝ) *
      ((parisiCDF μ s * backwardC β μ (s,x)) * backwardZ β μ (s,x)) := by
    unfold bridgeCrossingThirdFlux crossingThirdFlux actualCrossingPhi
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) le_rfl).trans
  simp only [norm_div,norm_mul,norm_pow,show ‖(2 : ℝ)‖ = 2 by norm_num,
    show ‖(11/2 : ℝ)‖ = 11/2 by norm_num]
  simp only [norm_mul] at hPhiN hprod
  simp only [div_eq_mul_inv] at hPhiN ⊢
  norm_num at hz3 hprod hPhiN ⊢
  nlinarith

/-- The normalized third-source mean is exactly the algebraic integrand
whose centering gives the two covariances. -/
theorem bridge_crossing_third_source_expectation (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ x, bridgeCrossingThirdSource β μ s x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
    (∫ x, actualCrossingPhi β μ (parisiCDF μ s) (s,x) * bridgeCrossingK β μ s hs x / 2 +
      backwardH β μ (parisiCDF μ s) (s,x) * bridgeCrossingPsi β μ s hs x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  let w := bridgeCrossingWeight β μ s hs
  let r := bridgeCrossingThirdSource β μ s
  let pK := fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x) * bridgeCrossingK β μ s hs x / 2
  let hP := fun x => backwardH β μ (parisiCDF μ s) (s,x) * bridgeCrossingPsi β μ s hs x
  have hw := bridgeCrossingWeight_integrable β hβ μ s hs
  have hp := fun x (_ : 0 < x) => bridgeCrossingWeight_pos β hβ μ s hs x
  have hr := integrable_weighted_of_crossingWeightLaw w r hw hp
    (integrable_bridgeCrossingThirdSource β hβ μ s hs)
  have hk := integrable_weighted_of_crossingWeightLaw w pK hw hp
    ((integrable_bridgeCrossingPhi_mul_K β hβ μ s hs).div_const 2)
  have hpsi := integrable_weighted_of_crossingWeightLaw w hP hw hp
    (integrable_bridgeCrossingH_mul_Psi β hβ μ s hs)
  have hi : IntegrableOn (fun x => (r x - pK x - hP x)*w x) (Ioi (0 : ℝ)) := by
    convert (hr.sub hk).sub hpsi using 1
    funext x
    dsimp only [Pi.sub_apply]
    ring
  have ht : Tendsto (fun x => bridgeCrossingThirdFlux β μ s hs x*w x) atTop (𝓝 0) := by
    apply tendsto_zero_of_crossingGaussianEnvelope_bound _ (β^2*s) 1
      (2*((3/2 : ℝ)*(β^2*s)⁻¹+12)*Real.exp (β^2)*(Real.sqrt (2*Real.pi*(β^2*s)))⁻¹)
      (mul_pos (sq_pos_of_ne_zero hβ) hs.1)
    intro x hx
    rw [norm_mul]
    have hg : ‖bridgeCrossingThirdFlux β μ s hs x‖ ≤
        ((3/2 : ℝ)*(β^2*s)⁻¹+12)*(1+|x|) := by
      apply (norm_bridgeCrossingThirdFlux_linear β hβ μ s hs x).trans
      rw [div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le,abs_nonneg x]
    apply (mul_le_mul hg (bridgeCrossingWeight_gaussian_envelope β hβ μ s hs x hx)
      (norm_nonneg _) (by have hv := mul_pos (sq_pos_of_ne_zero hβ) hs.1; positivity)).trans_eq
    unfold crossingGaussianEnvelope
    simp only [pow_zero,pow_one]
    ring
  have hd := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x (_ : x ∈ Ici (0 : ℝ)) => hasDerivAt_bridgeCrossingThirdFlux_weight β hβ μ s hs x) hi ht
  have hzero : bridgeCrossingThirdFlux β μ s hs 0 = 0 := by
    simp only [bridgeCrossingThirdFlux,crossingThirdFlux,backwardZ_at_zero β μ s ⟨hs.1.le,hs.2⟩,
      bridgeCrossingN_origin β hβ μ s hs,mul_zero,zero_pow (by norm_num : (3 : ℕ) ≠ 0),zero_div,sub_zero,zero_add]
  rw [hzero,zero_mul,sub_self] at hd
  have he : (fun x => (r x - pK x - hP x)*w x) =
      fun x => r x*w x-pK x*w x-hP x*w x := by funext x; ring
  have hOut := integral_sub (hr.sub hk) hpsi
  have hIn := integral_sub hr hk
  simp only [Pi.sub_apply] at hOut hIn
  rw [he,hOut,hIn] at hd
  rw [integral_crossingWeightLaw w r hw hp,integral_crossingWeightLaw w (fun x => pK x+hP x) hw hp]
  have hsadd : (fun x => (pK x+hP x)*w x) = fun x => pK x*w x+hP x*w x := by funext x;ring
  have hAdd := integral_add hk hpsi
  rw [hsadd,hAdd]
  congr 1
  linarith

end FRSB
