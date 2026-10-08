module

public import FRSB.CrossingActualWeightTime
public import FRSB.CrossingBridgeIntegrability
public import FRSB.ForwardDensityDomination

@[expose] public section

/-! Concrete decay and boundedness for the actual crossing transport.
The Gaussian envelope is uniform over all physical times bounded away
from zero, so it applies to every compact constant-mass interval. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

def crossingPhysicalPhiX (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) : ℝ :=
  2*backwardZ β μ (s,x)*(2*backwardQ β μ m (s,x)+3*m*backwardC β μ (s,x))
def crossingPhysicalPhiT (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) : ℝ :=
  β^2*(backwardQ β μ m (s,x)*actualCrossingPhi β μ m (s,x)+
    backwardZ β μ (s,x)*backwardHx β μ m (s,x)-
    actualCrossingVelocity β μ m (s,x)*crossingPhysicalPhiX β μ m s x)
def crossingPhysicalPhiWeightT (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) : ℝ :=
  crossingPhysicalPhiT β μ m s x*crossingPhysicalWeight β μ s x+
    actualCrossingPhi β μ m (s,x)*crossingPhysicalWeightT β μ m s x

theorem norm_actualCrossingVelocity_le_two (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖actualCrossingVelocity β μ (parisiCDF μ s) (s,x)‖ ≤ 2 := by
  have hB : ‖backwardB β μ (s,x)‖ ≤ 1 := by
    rw [backwardB_eq_gradient β μ s x hs]
    exact norm_parisiGradient_le_one β μ (s,x)
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  unfold actualCrossingVelocity
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
  nlinarith [parisiCDF_le_one μ s,parisiCDF_nonneg μ s,norm_nonneg (backwardB β μ (s,x))]

theorem norm_crossingCt_le_five_C (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖crossingCt (parisiCDF μ s) (backwardB β μ (s,x)) (backwardC β μ (s,x))
      (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x))‖ ≤ 5*backwardC β μ (s,x) := by
  have hC := (backwardC_pos β hβ μ s x hs).ne'
  have he := crossing_transport_C_from_jet (parisiCDF μ s) (backwardB β μ (s,x))
    (backwardC β μ (s,x)) (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x)) hC
  change crossingCt _ _ _ _ _+actualCrossingVelocity β μ (parisiCDF μ s) (s,x)*
    backwardD β μ 3 (s,x)=backwardC β μ (s,x)*backwardQ β μ (parisiCDF μ s) (s,x) at he
  rw [backwardD_three_eq_neg_two_C_z β hβ μ s x hs] at he
  have heq : crossingCt (parisiCDF μ s) (backwardB β μ (s,x)) (backwardC β μ (s,x))
      (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x)) = backwardC β μ (s,x)*
        (backwardQ β μ (parisiCDF μ s) (s,x)+2*actualCrossingVelocity β μ (parisiCDF μ s) (s,x)*
          backwardZ β μ (s,x)) := by
    rw [backwardD_three_eq_neg_two_C_z β hβ μ s x hs]
    linear_combination he
  rw [heq,norm_mul,Real.norm_of_nonneg (backwardC_pos β hβ μ s x hs).le]
  have hQ : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x hs
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hv := norm_actualCrossingVelocity_le_two β hβ μ s x hs
  rw [mul_comm (5 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (backwardC_pos β hβ μ s x hs).le
  apply (norm_add_le _ _).trans
  simp only [norm_mul,show ‖(2 : ℝ)‖=2 by norm_num]
  nlinarith [norm_nonneg (actualCrossingVelocity β μ (parisiCDF μ s) (s,x)),norm_nonneg (backwardZ β μ (s,x))]

theorem norm_crossingPhysicalPhiX_le_ten (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖crossingPhysicalPhiX β μ (parisiCDF μ s) s x‖ ≤ 10 := by
  have hQ : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x hs
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hmC : ‖parisiCDF μ s*backwardC β μ (s,x)‖ ≤ 1 := by
    rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s),
      Real.norm_of_nonneg (backwardC_pos β hβ μ s x hs).le]
    exact (mul_le_mul (parisiCDF_le_one μ s) (backwardC_le_one β hβ μ s x hs)
      (backwardC_pos β hβ μ s x hs).le zero_le_one).trans_eq (mul_one _)
  have hsum : ‖2*backwardQ β μ (parisiCDF μ s) (s,x)+
      3*(parisiCDF μ s*backwardC β μ (s,x))‖ ≤ 5 := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,show ‖(2 : ℝ)‖=2 by norm_num,show ‖(3 : ℝ)‖=3 by norm_num]
    rw [norm_mul] at hmC
    linarith
  unfold crossingPhysicalPhiX
  rw [show 3*parisiCDF μ s*backwardC β μ (s,x)=3*(parisiCDF μ s*backwardC β μ (s,x)) by ring,
    norm_mul,norm_mul,show ‖(2 : ℝ)‖=2 by norm_num]
  nlinarith [norm_nonneg (backwardZ β μ (s,x)),
    norm_nonneg (2*backwardQ β μ (parisiCDF μ s) (s,x)+3*(parisiCDF μ s*backwardC β μ (s,x)))]

theorem norm_crossingPhysicalPhiT_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    ‖crossingPhysicalPhiT β μ (parisiCDF μ s) s x‖ ≤ 29*β^2 := by
  have hQ : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x hs
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hHx : ‖backwardHx β μ (parisiCDF μ s) (s,x)‖ ≤ 6 := by
    rw [Real.norm_of_nonneg (backwardHx_bounds β hβ μ s x hs hx).1]
    exact (backwardHx_bounds β hβ μ s x hs hx).2.trans
      (by nlinarith [parisiCDF_nonneg μ s])
  have hPhi := norm_actualCrossingPhi_le_three β hβ μ s x hs
  have hv := norm_actualCrossingVelocity_le_two β hβ μ s x hs
  have hPhiX := norm_crossingPhysicalPhiX_le_ten β hβ μ s x hs
  unfold crossingPhysicalPhiT
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  rw [mul_comm (29 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  simp only [norm_mul]
  nlinarith [norm_nonneg (backwardQ β μ (parisiCDF μ s) (s,x)),
    norm_nonneg (actualCrossingPhi β μ (parisiCDF μ s) (s,x)),
    norm_nonneg (backwardZ β μ (s,x)),norm_nonneg (backwardHx β μ (parisiCDF μ s) (s,x)),
    norm_nonneg (actualCrossingVelocity β μ (parisiCDF μ s) (s,x)),
    norm_nonneg (crossingPhysicalPhiX β μ (parisiCDF μ s) s x)]

theorem hasDerivAt_crossingPhysicalPhiWeight_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s=m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r=>actualCrossingPhi β μ m (r,x)*crossingPhysicalWeight β μ r x)
      (crossingPhysicalPhiWeightT β μ m s x) s :=
  (hasDerivAt_actualCrossingPhi_constantCDF_time β hβ μ ha hab hb hc hs x).mul
    (hasDerivAt_crossingPhysicalWeight_time β hβ μ ha hab hb hc hs x)

theorem norm_crossingPhysicalWeight_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖crossingPhysicalWeight β μ s x‖ ≤ 2*‖parisiForwardDensity β μ s x‖ := by
  have hC : ‖backwardC β μ (s,x)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (backwardC_pos β hβ μ s x hs).le]
    exact backwardC_le_one β hβ μ s x hs
  unfold crossingPhysicalWeight
  simp only [norm_mul,norm_pow,show ‖(2 : ℝ)‖=2 by norm_num]
  have hC2 : ‖backwardC β μ (s,x)‖^2≤1 := pow_le_one₀ (norm_nonneg _) hC
  nlinarith [norm_nonneg (parisiForwardDensity β μ s x)]

theorem norm_crossingPhysicalWeightT_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖crossingPhysicalWeightT β μ (parisiCDF μ s) s x‖ ≤
      20*β^2*‖parisiForwardDensity β μ s x‖+2*‖parisiForwardDensityT β μ (parisiCDF μ s) s x‖ := by
  have hC : ‖backwardC β μ (s,x)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (backwardC_pos β hβ μ s x hs).le]
    exact backwardC_le_one β hβ μ s x hs
  have hCt : ‖crossingCt (parisiCDF μ s) (backwardB β μ (s,x)) (backwardC β μ (s,x))
      (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x))‖ ≤ 5 :=
    (norm_crossingCt_le_five_C β hβ μ s x hs).trans (by nlinarith [backwardC_le_one β hβ μ s x hs])
  unfold crossingPhysicalWeightT
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_pow,Real.norm_of_nonneg (sq_nonneg β),
    show ‖(4 : ℝ)‖=4 by norm_num,show ‖(2 : ℝ)‖=2 by norm_num]
  calc
    _ ≤ 4*1*(β^2*5)*‖parisiForwardDensity β μ s x‖+
      2*1^2*‖parisiForwardDensityT β μ (parisiCDF μ s) s x‖ := by gcongr
    _ = _ := by ring

theorem norm_crossingPhysicalPhiWeightT_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    ‖crossingPhysicalPhiWeightT β μ (parisiCDF μ s) s x‖ ≤
      118*β^2*‖parisiForwardDensity β μ s x‖+6*‖parisiForwardDensityT β μ (parisiCDF μ s) s x‖ := by
  have hPhiT := norm_crossingPhysicalPhiT_le β hβ μ s x hs hx
  have hw := norm_crossingPhysicalWeight_le β hβ μ s x hs
  have hPhi := norm_actualCrossingPhi_le_three β hβ μ s x hs
  have hwT := norm_crossingPhysicalWeightT_le β hβ μ s x hs
  unfold crossingPhysicalPhiWeightT
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  calc
    _ ≤ (29*β^2)*(2*‖parisiForwardDensity β μ s x‖)+
      3*(20*β^2*‖parisiForwardDensity β μ s x‖+2*‖parisiForwardDensityT β μ (parisiCDF μ s) s x‖) := by gcongr
    _ = _ := by ring

def crossingCompactDecayConstant (β l : ℝ) : ℝ :=
  1+2*forwardCompactDensityConstant β l+138*β^2*forwardCompactDensityConstant β l+
    8*forwardCompactTimeConstant β l

theorem crossingCompactDecayConstant_pos (β l : ℝ) : 0<crossingCompactDecayConstant β l := by
  unfold crossingCompactDecayConstant
  positivity [forwardCompactDensityConstant_nonneg β l,forwardCompactTimeConstant_nonneg β l]

/-- The precise polynomial Gaussian decay, uniformly on any time range
bounded away from zero. The coefficient is independent of the measure. -/
theorem crossing_actual_decay_bound (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (l : ℝ) (hl : 0<l) {s x : ℝ} (hs : s ∈ Icc l 1) (hx : 0≤x) :
    crossingPhysicalWeight β μ s x+
      ‖crossingPhysicalWeightT β μ (parisiCDF μ s) s x‖+
      ‖crossingPhysicalPhiWeightT β μ (parisiCDF μ s) s x‖ ≤
        crossingCompactDecayConstant β l*crossingGaussianEnvelope (β^2) 2 x := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hl.le.trans hs.1,hs.2⟩
  have hp := norm_parisiForwardDensity_compact_time_bound β hβ μ hl (le_refl (1 : ℝ)) hs hx
  have hpt := norm_parisiForwardDensityT_compact_time_bound β hβ μ hl (le_refl (1 : ℝ))
    ⟨parisiCDF_nonneg μ s,parisiCDF_le_one μ s⟩ hs hx
  simp only [mul_one] at hp hpt
  have hw : crossingPhysicalWeight β μ s x≤2*‖parisiForwardDensity β μ s x‖ :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      norm_crossingPhysicalWeight_le β hβ μ s x ht)
  have hwT := norm_crossingPhysicalWeightT_le β hβ μ s x ht
  have hPhiwT := norm_crossingPhysicalPhiWeightT_le β hβ μ s x ht hx
  have he : 0≤crossingGaussianEnvelope (β^2) 2 x := by unfold crossingGaussianEnvelope;positivity
  have hβ2 := sq_nonneg β
  have hd := forwardCompactDensityConstant_nonneg β l
  have hdt := forwardCompactTimeConstant_nonneg β l
  calc
    _ ≤ 2*(forwardCompactDensityConstant β l*crossingGaussianEnvelope (β^2) 2 x)+
      (20*β^2*(forwardCompactDensityConstant β l*crossingGaussianEnvelope (β^2) 2 x)+
        2*(forwardCompactTimeConstant β l*crossingGaussianEnvelope (β^2) 2 x))+
      (118*β^2*(forwardCompactDensityConstant β l*crossingGaussianEnvelope (β^2) 2 x)+
        6*(forwardCompactTimeConstant β l*crossingGaussianEnvelope (β^2) 2 x)) := by
      gcongr
      · exact hw.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
      · apply hwT.trans
        gcongr
      · apply hPhiwT.trans
        gcongr
    _ ≤ _ := by unfold crossingCompactDecayConstant; nlinarith

theorem crossing_actual_bounded_fields (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0≤x) :
    ‖actualCrossingVelocity β μ (parisiCDF μ s) (s,x)‖≤2 ∧
    ‖backwardZ β μ (s,x)‖≤1 ∧
    ‖actualCrossingPhi β μ (parisiCDF μ s) (s,x)‖≤3 ∧
    ‖crossingPhysicalPhiX β μ (parisiCDF μ s) s x‖≤10 ∧
    ‖backwardQ β μ (parisiCDF μ s) (s,x)*actualCrossingPhi β μ (parisiCDF μ s) (s,x)+
      backwardZ β μ (s,x)*backwardHx β μ (parisiCDF μ s) (s,x)‖≤9 ∧
    ‖backwardH β μ (parisiCDF μ s) (s,x)‖≤4 := by
  have hQ : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖≤1 := by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x hs
  have hz : ‖backwardZ β μ (s,x)‖≤1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hPhi := norm_actualCrossingPhi_le_three β hβ μ s x hs
  have hHx : ‖backwardHx β μ (parisiCDF μ s) (s,x)‖≤6 := by
    rw [Real.norm_of_nonneg (backwardHx_bounds β hβ μ s x hs hx).1]
    exact (backwardHx_bounds β hβ μ s x hs hx).2.trans (by nlinarith [parisiCDF_nonneg μ s])
  refine ⟨norm_actualCrossingVelocity_le_two β hβ μ s x hs,hz,hPhi,
    norm_crossingPhysicalPhiX_le_ten β hβ μ s x hs,?_,norm_backwardH_le_four_crossing β hβ μ s x hs⟩
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  nlinarith [norm_nonneg (backwardQ β μ (parisiCDF μ s) (s,x)),
    norm_nonneg (actualCrossingPhi β μ (parisiCDF μ s) (s,x)),
    norm_nonneg (backwardZ β μ (s,x)),norm_nonneg (backwardHx β μ (parisiCDF μ s) (s,x))]

theorem crossing_actual_origin (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    actualCrossingVelocity β μ (parisiCDF μ s) (s,0)=0 ∧ backwardZ β μ (s,0)=0 := by
  simp only [actualCrossingVelocity,backwardB_at_zero β hβ μ s hs,
    backwardZ_at_zero β μ s hs,mul_zero,sub_zero,and_self]

def crossingClockDecayConstant (β l : ℝ) : ℝ :=
  (1+(β^2)⁻¹)*crossingCompactDecayConstant β l

theorem crossingClockDecayConstant_pos (β : ℝ) (hβ : β≠0) (l : ℝ) :
    0<crossingClockDecayConstant β l := by
  unfold crossingClockDecayConstant
  exact mul_pos (by positivity) (crossingCompactDecayConstant_pos β l)

theorem crossing_actual_clock_source_decay_bound (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    (l : ℝ) (hl : 0<l) {s x : ℝ} (hs : s∈Icc l 1) (hx : 0≤x) :
    crossingPhysicalWeight β μ s x+
      ‖crossingPhysicalWeightT β μ (parisiCDF μ s) s x/β^2‖+
      ‖crossingPhysicalPhiWeightT β μ (parisiCDF μ s) s x/β^2‖ ≤
        crossingClockDecayConstant β l*crossingGaussianEnvelope (β^2) 2 x := by
  have hdec := crossing_actual_decay_bound β hβ μ l hl hs hx
  have hw : 0≤crossingPhysicalWeight β μ s x := by
    rw [crossingPhysicalWeight_eq β μ ⟨hl.trans_le hs.1,hs.2⟩]
    exact (bridgeCrossingWeight_pos β hβ μ s ⟨hl.trans_le hs.1,hs.2⟩ x).le
  have hb : 0≤(β^2)⁻¹ := inv_nonneg.mpr (sq_nonneg β)
  simp only [div_eq_mul_inv,norm_mul,Real.norm_of_nonneg hb]
  unfold crossingClockDecayConstant
  calc
    _ ≤ (1+(β^2)⁻¹)*(crossingPhysicalWeight β μ s x+
      ‖crossingPhysicalWeightT β μ (parisiCDF μ s) s x‖+
      ‖crossingPhysicalPhiWeightT β μ (parisiCDF μ s) s x‖) := by
      nlinarith [mul_nonneg hb hw,norm_nonneg (crossingPhysicalWeightT β μ (parisiCDF μ s) s x),
        norm_nonneg (crossingPhysicalPhiWeightT β μ (parisiCDF μ s) s x)]
    _ ≤ (1+(β^2)⁻¹)*(crossingCompactDecayConstant β l*crossingGaussianEnvelope (β^2) 2 x) :=
      mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by ring

end FRSB
