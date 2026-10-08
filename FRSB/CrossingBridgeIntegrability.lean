module

public import FRSB.CrossingBridgeDifferentiation
public import FRSB.TerminalAtomCentering

@[expose] public section

/-! Genuine Gaussian-tail integrability and vanishing spatial flux for
crossing observables built from the actual selected PDE and bridge density. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

theorem norm_mass_mul_C_le_one (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖parisiCDF μ s * backwardC β μ (s,x)‖ ≤ 1 := by
  rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s),
    Real.norm_of_nonneg (backwardC_pos β hβ μ s x hs).le]
  exact (mul_le_mul (parisiCDF_le_one μ s) (backwardC_le_one β hβ μ s x hs)
    (backwardC_pos β hβ μ s x hs).le zero_le_one).trans_eq (mul_one _)

theorem norm_actualCrossingPhi_le_three (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖actualCrossingPhi β μ (parisiCDF μ s) (s,x)‖ ≤ 3 := by
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hzs : ‖backwardZ β μ (s,x)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  unfold actualCrossingPhi crossingPhi
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_pow,show ‖(2 : ℝ)‖ = 2 by norm_num]
  linarith [norm_mass_mul_C_le_one β hβ μ s x hs]

theorem norm_backwardH_le_four_crossing (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖backwardH β μ (parisiCDF μ s) (s,x)‖ ≤ 4 := by
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x hs
  have hzs : ‖backwardZ β μ (s,x) ^ 2‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  have hQ : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x hs
  rw [backwardH_eq_z_sq_mC_sub_twoQ]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  rw [norm_mul (2 : ℝ),show ‖(2 : ℝ)‖ = 2 by norm_num]
  linarith [norm_mass_mul_C_le_one β hβ μ s x hs]

theorem norm_bridgeCrossingN_linear (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖bridgeCrossingN β μ s hs x‖ ≤ |x| / (β ^ 2 * s) + 3 := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x ht
  have hB : ‖backwardB β μ (s,x)‖ ≤ 1 := by
    rw [backwardB_eq_gradient β μ s x ht]
    exact norm_parisiGradient_le_one β μ _
  have hmB : ‖parisiCDF μ s * backwardB β μ (s,x)‖ ≤ 1 := by
    rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s)]
    exact (mul_le_mul (parisiCDF_le_one μ s) hB (norm_nonneg _) zero_le_one).trans_eq (mul_one _)
  unfold bridgeCrossingN
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  linarith [bridgeCrossingVx_norm_le β hβ μ s hs x]

theorem norm_bridgeCrossingPsi_linear (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖bridgeCrossingPsi β μ s hs x‖ ≤ |x| / (β ^ 2 * s) + 5 := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x ht
  have hQ : ‖backwardQ β μ (parisiCDF μ s) (s,x)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x ht
  unfold bridgeCrossingPsi
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  apply (add_le_add (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) le_rfl).trans
  rw [one_mul]
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  linarith [norm_bridgeCrossingN_linear β hβ μ s hs x]

/-- Every actual observable with polynomial growth is integrable against
this genuine normalized bridge-curvature weight. -/
theorem integrable_bridgeCrossingWeightLaw_of_polynomial_growth
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (f : ℝ → ℝ) (hf : Continuous f)
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ x > 0, ‖f x‖ ≤ K * (1 + |x| ^ n)) :
    Integrable f (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  apply integrable_crossingWeightLaw_of_weighted _ _
    (bridgeCrossingWeight_integrable β hβ μ s hs)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x)
  let A := Real.exp (β ^ 2) * (Real.sqrt (2 * Real.pi * (β ^ 2 * s)))⁻¹
  apply integrableOn_of_crossingGaussianEnvelope_bound _ (β^2*s) n (2*K*A)
    (mul_pos (sq_pos_of_ne_zero hβ) hs.1)
  · exact (hf.mul (continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_bridgeCrossingWeight β hβ μ s hs x).continuousAt))).aestronglyMeasurable
  · intro x hx
    rw [norm_mul]
    calc
      _ ≤ (K * (1 + |x| ^ n)) * (A * crossingGaussianEnvelope (β^2*s) 0 x) :=
        mul_le_mul (hb x hx) (bridgeCrossingWeight_gaussian_envelope β hβ μ s hs x hx)
          (norm_nonneg _) (mul_nonneg hK (by positivity))
      _ = _ := by unfold crossingGaussianEnvelope; simp only [pow_zero]; ring

theorem integrable_bridgeCrossingPhi (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x))
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  apply integrable_bridgeCrossingWeightLaw_of_polynomial_growth β hβ μ s hs _
    (continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_actualCrossingPhi β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩).continuousAt))
    0 3 (by norm_num)
  intro x _
  simpa only [pow_zero] using (norm_actualCrossingPhi_le_three β hβ μ s x ⟨hs.1.le,hs.2⟩).trans
    (by norm_num : (3 : ℝ) ≤ 3 * (1+1))

theorem integrable_bridgeCrossingPsi (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (bridgeCrossingPsi β μ s hs)
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  apply integrable_bridgeCrossingWeightLaw_of_polynomial_growth β hβ μ s hs _
    (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_bridgeCrossingPsi β hβ μ s hs x).continuousAt))
    1 ((β^2*s)⁻¹+5) (by have hv := mul_pos (sq_pos_of_ne_zero hβ) hs.1; positivity)
  intro x _
  apply (norm_bridgeCrossingPsi_linear β hβ μ s hs x).trans
  rw [pow_one,div_eq_mul_inv]
  nlinarith [inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le,abs_nonneg x]

/-- Actual centering on every positive physical time, obtained by the
exact flux derivative and the Gaussian tail rather than presumed. -/
theorem bridge_crossing_centering (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ x, bridgeCrossingPsi β μ s hs x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
      -(∫ x, actualCrossingPhi β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  have hcΦ : Continuous (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x)) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (hasDerivAt_actualCrossingPhi β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩).continuousAt)
  have hcΨ : Continuous (bridgeCrossingPsi β μ s hs) :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_bridgeCrossingPsi β hβ μ s hs x).continuousAt)
  apply crossing_centered_expectation_from_IBP _ _ _
    (fun x => bridgeCrossingWeight β μ s hs x * backwardZ β μ (s,x))
    (bridgeCrossingWeight_integrable β hβ μ s hs)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x)
  · apply integrableOn_mul_bridgeCrossingWeight_of_linear_growth β hβ μ s hs _ hcΦ 3 (by norm_num)
    intro x _
    exact (norm_actualCrossingPhi_le_three β hβ μ s x ⟨hs.1.le,hs.2⟩).trans
      (by nlinarith [abs_nonneg x])
  · apply integrableOn_mul_bridgeCrossingWeight_of_linear_growth β hβ μ s hs _ hcΨ
      ((β^2*s)⁻¹+5) (by have hv := mul_pos (sq_pos_of_ne_zero hβ) hs.1; positivity)
    intro x _
    apply (norm_bridgeCrossingPsi_linear β hβ μ s hs x).trans
    rw [div_eq_mul_inv]
    nlinarith [inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le,abs_nonneg x]
  · exact fun x _ => hasDerivAt_bridgeCrossingWeight_mul_z β hβ μ s hs x
  · rw [backwardZ_at_zero β μ s ⟨hs.1.le,hs.2⟩,mul_zero]
  · apply tendsto_zero_of_crossingGaussianEnvelope_bound _ (β^2*s) 0
      (Real.exp (β^2)*(Real.sqrt (2*Real.pi*(β^2*s)))⁻¹)
      (mul_pos (sq_pos_of_ne_zero hβ) hs.1)
    intro x hx
    rw [norm_mul]
    have hz : ‖backwardZ β μ (s,x)‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans
      (by simpa only [mul_one] using bridgeCrossingWeight_gaussian_envelope β hβ μ s hs x hx)

end FRSB
