module

public import FRSB.ForwardDensityLaw
public import FRSB.TerminalHalfLine
public import FRSB.GammaHigher
public import FRSB.CrossingStrictSource
public import FRSB.BackwardsTime

@[expose] public section

/-! The actual diffusion law, its curvature-square tilt, and the normalized
positive-half-line crossing law have exactly the same even observables.
The normalization is the genuine curvature second moment. This identifies
the crossing means with the actual second and third Gamma expressions. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

 theorem bridgeCrossingWeight_even (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    bridgeCrossingWeight β μ s hs (-x) = bridgeCrossingWeight β μ s hs x := by
  unfold bridgeCrossingWeight backwardC
  rw [backwardD_reflect β μ s ⟨hs.1.le,hs.2⟩ 2 x,forwardBridgeDensity_even]
  norm_num

 theorem selectedItoState_eq_optimalStateReal (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (sample : BrownianSample) :
    selectedParisiItoState β 0 hβ μ s.toNNReal sample = optimalStateReal β μ sample s := by
  rw [← optimalState_eq_selected β hβ μ,
    optimalState_eq_real β μ (by simpa only [Real.coe_toNNReal s hs.1] using hs.2),
    Real.coe_toNNReal s hs.1]

 theorem backwardD_state_eq_jetProcess (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (s : ℝ) (sample : BrownianSample) :
    backwardD β μ j (s,optimalStateReal β μ sample s) = jetProcess β μ j s sample :=
  backwardD_eq_spatialJet β μ j s _

/-- No boundedness restriction on the Borel observable is needed for this
identity: both sides use the same Bochner-integral convention. In particular
it applies to every even observable integrable under the curvature tilt. -/
 theorem integral_halfLine_bridgeCrossingWeight_even (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : Measurable f) (he : ∀ x,f (-x) = f x) :
    (∫ x in Ioi (0 : ℝ),f x * bridgeCrossingWeight β μ s hs x) =
      ∫ sample,C β μ s sample ^ 2 * f (optimalStateReal β μ sample s)
        ∂canonicalBrownianMeasure := by
  have hC : Continuous (fun x => backwardC β μ (s,x)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le,hs.2⟩).continuousAt
  have hd := integral_selectedState_bridgeDensity β hβ μ s hs
    (fun x => backwardC β μ (s,x) ^ 2 * f x) ((hC.measurable.pow_const 2).mul hf)
  have hi : (∫ x,f x * bridgeCrossingWeight β μ s hs x) =
      2 * (∫ x,forwardBridgeDensity β μ s hs x *
        (backwardC β μ (s,x) ^ 2 * f x)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun x => by unfold bridgeCrossingWeight; ring
  have hp := integral_eq_two_mul_halfLine_of_even
    (fun x => f x * bridgeCrossingWeight β μ s hs x)
    (fun x => by rw [he x,bridgeCrossingWeight_even β μ s hs x])
  have hm : (∫ sample,backwardC β μ
        (s,selectedParisiItoState β 0 hβ μ s.toNNReal sample) ^ 2 *
        f (selectedParisiItoState β 0 hβ μ s.toNNReal sample)
        ∂canonicalBrownianMeasure) =
      ∫ sample,C β μ s sample ^ 2 * f (optimalStateReal β μ sample s)
        ∂canonicalBrownianMeasure := by
    apply integral_congr_ae
    exact .of_forall fun sample => by
      dsimp only
      rw [selectedItoState_eq_optimalStateReal β hβ μ s ⟨hs.1.le,hs.2⟩ sample]
      change backwardD β μ 2 (s,optimalStateReal β μ sample s) ^ 2 * _ = _
      rw [backwardD_state_eq_jetProcess]
  rw [← hd,hm] at hi
  linarith

 theorem crossingWeightMass_bridge_eq_curvatureMoment2 (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    crossingWeightMass (bridgeCrossingWeight β μ s hs) = curvatureMoment2 β μ s := by
  simpa only [one_mul,mul_one,crossingWeightMass,curvatureMoment2] using
    integral_halfLine_bridgeCrossingWeight_even β hβ μ s hs (fun _ => 1)
      measurable_const (fun _ => rfl)

 theorem integral_bridgeCrossingWeightLaw_even (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : Measurable f) (he : ∀ x,f (-x) = f x) :
    (∫ x,f x ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
      (∫ sample,C β μ s sample ^ 2 * f (optimalStateReal β μ sample s)
        ∂canonicalBrownianMeasure) / curvatureMoment2 β μ s := by
  rw [integral_crossingWeightLaw _ _ (bridgeCrossingWeight_integrable β hβ μ s hs)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x),
    integral_halfLine_bridgeCrossingWeight_even β hβ μ s hs f hf he,
    crossingWeightMass_bridge_eq_curvatureMoment2 β hβ μ s hs]

/-- Integrability also transfers from the actual curvature-square tilt;
this applies to unbounded Borel observables. -/
 theorem integrable_bridgeCrossingWeightLaw_of_curvature_tilt (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun sample => C β μ s sample ^ 2 *
      f (optimalStateReal β μ sample s)) canonicalBrownianMeasure) :
    Integrable f (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  have hC : Continuous (fun x => backwardC β μ (s,x)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le,hs.2⟩).continuousAt
  let ψ : ℝ → ℝ := fun x => backwardC β μ (s,x)^2 * f x
  have hψ : Measurable ψ := (hC.measurable.pow_const 2).mul hf
  have hψcomp : Integrable (ψ ∘ selectedParisiItoState β 0 hβ μ s.toNNReal)
      canonicalBrownianMeasure := by
    convert hi using 1
    funext sample
    dsimp [ψ,Function.comp_def]
    rw [selectedItoState_eq_optimalStateReal β hβ μ s ⟨hs.1.le,hs.2⟩ sample]
    change backwardD β μ 2 (s,optimalStateReal β μ sample s)^2 * _ = _
    rw [backwardD_state_eq_jetProcess]
  have hψmap := (integrable_map_measure hψ.aestronglyMeasurable
    (measurable_selectedParisiState_time β 0 hβ μ s.toNNReal).aemeasurable).mpr hψcomp
  rw [selectedState_endpoint_eq_bridgeDensity β hβ μ s hs] at hψmap
  have hweighted := (integrable_withDensity_iff
    (contDiff_forwardBridgeDensity β μ s hs).continuous.measurable.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hψmap
  have hprod : Integrable (fun x => ψ x * forwardBridgeDensity β μ s hs x) := by
    simpa only [ENNReal.toReal_ofReal (forwardBridgeDensity_pos β hβ μ s hs _).le]
      using hweighted
  apply integrable_crossingWeightLaw_of_weighted _ _
    (bridgeCrossingWeight_integrable β hβ μ s hs)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x)
  convert (hprod.const_mul 2).integrableOn using 1
  funext x
  dsimp [ψ,bridgeCrossingWeight]
  ring

 theorem actualCrossingPhi_even (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    actualCrossingPhi β μ m (s,-x) = actualCrossingPhi β μ m (s,x) := by
  unfold actualCrossingPhi crossingPhi
  rw [backwardZ_odd β μ s x hs]
  unfold backwardC
  rw [backwardD_reflect β μ s hs 2 x]
  norm_num

 theorem bridgeCrossingThirdSource_even (β : ℝ) (μ : ParisiMeasure) (s x : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    bridgeCrossingThirdSource β μ s (-x) = bridgeCrossingThirdSource β μ s x := by
  unfold bridgeCrossingThirdSource crossingThirdSource
  change 2 * (actualCrossingPhi β μ (parisiCDF μ s) (s,-x) -
    backwardQ β μ (parisiCDF μ s) (s,-x)) ^ 2 -
      24 * parisiCDF μ s * backwardC β μ (s,-x) * backwardZ β μ (s,-x) ^ 2 +
      3 * parisiCDF μ s ^ 2 * backwardC β μ (s,-x) ^ 2 = _
  rw [actualCrossingPhi_even β μ _ s x hs,backwardQ_even β μ _ s x hs,
    backwardZ_odd β μ s x hs]
  unfold backwardC
  rw [backwardD_reflect β μ s hs 2 x]
  norm_num
  rfl

 theorem curvature_sq_crossingPhi_jet (m c d : ℝ) (hc : c ≠ 0) :
    c ^ 2 * crossingPhi m c (backwardZJet c d) = (d ^ 2 - 2*m*c^3) / 2 := by
  unfold crossingPhi backwardZJet
  field_simp

 theorem curvature_sq_crossingSource_jet (m c d e : ℝ) (hc : c ≠ 0) :
    2*c^2 * crossingThirdSource m c (backwardZJet c d) (backwardQJet m c d e) =
      e^2 - 12*m*c*d^2 + 6*m^2*c^4 := by
  unfold crossingThirdSource crossingPhi backwardZJet backwardQJet backwardZxJet
  field_simp
  ring

 private theorem quotient_scaled_curvature_moment (I Z b : ℝ) (hb : b ≠ 0) :
    (I / 2) / Z = b * I / (2*b*Z) := by
  field_simp

 theorem integral_crossingPhi_eq_GammaSecond (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ x,actualCrossingPhi β μ (parisiCDF μ s) (s,x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
      GammaSecond β μ s /
        (2*β^4*crossingWeightMass (bridgeCrossingWeight β μ s hs)) := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hf : Measurable (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x)) :=
    (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_actualCrossingPhi β hβ μ _ s x ht).continuousAt).measurable
  rw [integral_bridgeCrossingWeightLaw_even β hβ μ s hs _ hf
    (fun x => actualCrossingPhi_even β μ _ s x ht),
    GammaSecond_eq_integral β hβ μ ht,
    crossingWeightMass_bridge_eq_curvatureMoment2 β hβ μ s hs]
  have hi : (∫ sample,C β μ s sample ^ 2 *
      actualCrossingPhi β μ (parisiCDF μ s) (s,optimalStateReal β μ sample s)
      ∂canonicalBrownianMeasure) =
      (∫ sample,D β μ s sample ^ 2 - 2*parisiCDF μ s*C β μ s sample ^ 3
        ∂canonicalBrownianMeasure) / 2 := by
    rw [← integral_div]
    apply integral_congr_ae
    exact .of_forall fun sample => by
      have h := curvature_sq_crossingPhi_jet (parisiCDF μ s)
        (backwardC β μ (s,optimalStateReal β μ sample s))
        (backwardD β μ 3 (s,optimalStateReal β μ sample s))
        (backwardC_pos β hβ μ s _ ht).ne'
      simpa only [actualCrossingPhi,backwardZ,backwardC,
        backwardD_state_eq_jetProcess] using h
  rw [hi]
  exact quotient_scaled_curvature_moment _ _ _ (pow_ne_zero 4 hβ)

 theorem integral_crossingThirdSource_eq_GammaThird (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ x,bridgeCrossingThirdSource β μ s x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
      GammaThird β μ (parisiCDF μ s) s /
        (2*β^6*crossingWeightMass (bridgeCrossingWeight β μ s hs)) := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  rw [integral_bridgeCrossingWeightLaw_even β hβ μ s hs _
    (continuous_bridgeCrossingThirdSource β hβ μ s ht).measurable
    (fun x => bridgeCrossingThirdSource_even β μ s x ht),GammaThird_eq_integral,
    crossingWeightMass_bridge_eq_curvatureMoment2 β hβ μ s hs]
  have hi : (∫ sample,C β μ s sample ^ 2 *
      bridgeCrossingThirdSource β μ s (optimalStateReal β μ sample s)
      ∂canonicalBrownianMeasure) =
      (∫ sample,A β μ s sample^2 - 12*parisiCDF μ s*C β μ s sample*D β μ s sample^2 +
        6*parisiCDF μ s^2*C β μ s sample^4 ∂canonicalBrownianMeasure) / 2 := by
    rw [← integral_div]
    apply integral_congr_ae
    exact .of_forall fun sample => by
      have h := curvature_sq_crossingSource_jet (parisiCDF μ s)
        (backwardC β μ (s,optimalStateReal β μ sample s))
        (backwardD β μ 3 (s,optimalStateReal β μ sample s))
        (backwardD β μ 4 (s,optimalStateReal β μ sample s))
        (backwardC_pos β hβ μ s _ ht).ne'
      simp only [backwardC,backwardD_state_eq_jetProcess] at h
      change C β μ s sample^2 *
        crossingThirdSource _ (C β μ s sample)
          (backwardZJet (C β μ s sample) (D β μ s sample))
          (backwardQJet _ (C β μ s sample) (D β μ s sample) (A β μ s sample)) = _
      linarith
  rw [hi]
  exact quotient_scaled_curvature_moment _ _ _ (pow_ne_zero 6 hβ)

 theorem GammaThird_pos_of_GammaSecond_zero (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hm : 0 < parisiCDF μ s) (hz : GammaSecond β μ s = 0) :
    0 < GammaThird β μ (parisiCDF μ s) s := by
  have hzero : (∫ x,actualCrossingPhi β μ (parisiCDF μ s) (s,x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) = 0 := by
    rw [integral_crossingPhi_eq_GammaSecond β hβ μ s hs,hz,zero_div]
  have hp := bridge_crossing_source_pos_at_zero β hβ μ s hs hm hzero
  rw [integral_crossingThirdSource_eq_GammaThird β hβ μ s hs] at hp
  exact (div_pos_iff_of_pos_right (mul_pos (mul_pos (by norm_num)
    (pow_pos (sq_pos_of_ne_zero hβ) 3 |>.trans_eq (by ring)))
      (crossingWeightMass_pos _ (bridgeCrossingWeight_integrable β hβ μ s hs)
        (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x)))).mp hp

end FRSB
