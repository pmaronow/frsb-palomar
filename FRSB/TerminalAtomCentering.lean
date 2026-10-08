module

public import FRSB.TerminalOverlap
public import FRSB.CrossingBridgeFields
public import FRSB.CrossingRepresentation
public import FRSB.ForwardBridgeParity

@[expose] public section

/-! Genuine terminal-profile centering for the concrete bridge density.
The parameter m is the mass strictly below the terminal overlap. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

def terminalCrossingPhi (m x : ℝ) : ℝ := 2 * Real.tanh x ^ 2 - m * sech x ^ 2

def terminalCrossingPsi (β : ℝ) (μ : ParisiMeasure) (q : ℝ)
    (hq : q ∈ Ioc (0 : ℝ) 1) (m x : ℝ) : ℝ :=
  Real.tanh x * bridgeCrossingVx β μ q hq x + Real.tanh x ^ 2 - (1-m) * sech x ^ 2

theorem backwardZ_terminal_overlap (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (x : ℝ) :
    backwardZ β μ (q,x) = Real.tanh x := by
  have hc := parisiHessian_terminal_region β hβ μ hq hmax ⟨le_rfl,hq.2⟩ x
  have hd := parisiSpatialJet_three_terminal_region β hβ μ hq hmax ⟨le_rfl,hq.2⟩ x
  have he : backwardD β μ 3 (q,x) = -2 * Real.tanh x * sech x ^ 2 := by
    exact hd
  rw [backwardZ, backwardZJet, backwardC_eq_hessian β μ q x hq, hc, he]
  have hp : sech x ^ 2 ≠ 0 := (sq_pos_of_pos (sech_pos x)).ne'
  field_simp [(sech_pos x).ne']

theorem bridgeCrossingVx_norm_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (q : ℝ) (hq : q ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖bridgeCrossingVx β μ q hq x‖ ≤ |x| / (β ^ 2 * q) + 1 := by
  unfold bridgeCrossingVx
  apply (norm_add_le _ _).trans
  rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg
    (mul_pos (sq_pos_of_ne_zero hβ) hq.1).le]
  exact add_le_add_right (forwardBridgeCorrection_slope_bound β μ q hq x) _

theorem integrableOn_mul_bridgeCrossingWeight_of_linear_growth
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (q : ℝ) (hq : q ∈ Ioc (0 : ℝ) 1) (f : ℝ → ℝ) (hf : Continuous f)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x > 0, ‖f x‖ ≤ K * (1 + |x|)) :
    IntegrableOn (fun x => f x * bridgeCrossingWeight β μ q hq x) (Ioi (0 : ℝ)) := by
  let A := Real.exp (β ^ 2) * (Real.sqrt (2 * Real.pi * (β ^ 2 * q)))⁻¹
  apply integrableOn_of_crossingGaussianEnvelope_bound _ (β^2*q) 1 (2*K*A)
    (mul_pos (sq_pos_of_ne_zero hβ) hq.1)
  · have hw : Continuous (bridgeCrossingWeight β μ q hq) :=
      continuous_iff_continuousAt.mpr (fun x =>
        (hasDerivAt_bridgeCrossingWeight β hβ μ q hq x).continuousAt)
    exact (hf.mul hw).aestronglyMeasurable
  · intro x hx
    rw [norm_mul]
    calc
      _ ≤ (K*(1+|x|)) * (A * crossingGaussianEnvelope (β^2*q) 0 x) :=
        mul_le_mul (hb x hx) (bridgeCrossingWeight_gaussian_envelope β hβ μ q hq x hx)
          (norm_nonneg _) (mul_nonneg hK (by positivity))
      _ = _ := by
        unfold crossingGaussianEnvelope
        simp only [pow_zero,pow_one]
        ring

theorem norm_terminalCrossingPhi_le (m x : ℝ) :
    ‖terminalCrossingPhi m x‖ ≤ 2 + |m| := by
  have hb : ‖Real.tanh x‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
  have hc : ‖sech x ^ 2‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sech_sq_le_one x
  calc
    _ ≤ ‖2 * Real.tanh x ^ 2‖ + ‖m * sech x ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 + |m| := by
      simp only [norm_mul,norm_pow,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have ht : ‖Real.tanh x‖^2 ≤ 1 := by nlinarith [norm_nonneg (Real.tanh x)]
      have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg m)
      simpa only [mul_one,Real.norm_eq_abs,abs_pow] using add_le_add (mul_le_mul_of_nonneg_left ht
        (by norm_num : (0:ℝ) ≤ 2)) hm

theorem terminal_crossing_centering (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {q : ℝ} (hq : q ∈ Ioc (0 : ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (m : ℝ) :
    (∫ x, terminalCrossingPsi β μ q hq m x ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) =
      -(∫ x, terminalCrossingPhi m x ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) := by
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hq.1.le,hq.2⟩
  have hB : ∀ x, backwardB β μ (q,x) = Real.tanh x := fun x => by
    rw [backwardB_eq_gradient β μ q x hq']
    exact parisiGradient_terminal_region β hβ μ hq' hmax ⟨le_rfl,hq.2⟩ x
  have hC : ∀ x, backwardC β μ (q,x) = sech x ^ 2 := fun x => by
    rw [backwardC_eq_hessian β μ q x hq']
    exact parisiHessian_terminal_region β hβ μ hq' hmax ⟨le_rfl,hq.2⟩ x
  have hz : ∀ x, backwardZ β μ (q,x) = Real.tanh x :=
    backwardZ_terminal_overlap β hβ μ hq' hmax
  have hzder : ∀ x, backwardZx β μ (q,x) = sech x ^ 2 := fun x => by
    have hd := hasDerivAt_backwardZ β hβ μ q x hq'
    have he : (fun y => backwardZ β μ (q,y)) = Real.tanh := funext hz
    rw [he] at hd
    exact hd.unique (hasDerivAt_tanh x)
  have hcdf : parisiCDF μ q = 1 := parisiCDF_eq_one_above_support μ hmax le_rfl
  have hiPhi : IntegrableOn (fun x => terminalCrossingPhi m x *
      bridgeCrossingWeight β μ q hq x) (Ioi (0:ℝ)) := by
    apply integrableOn_mul_bridgeCrossingWeight_of_linear_growth β hβ μ q hq _
      (by
        unfold terminalCrossingPhi
        exact (continuous_const.mul (gaussian_continuous_tanh.pow 2)).sub
          (continuous_const.mul (gaussian_continuous_sech.pow 2)))
      (2+|m|) (by positivity)
    intro x hx
    exact (norm_terminalCrossingPhi_le m x).trans
      (by nlinarith [abs_nonneg x, abs_nonneg m])
  have hcV : Continuous (bridgeCrossingVx β μ q hq) := by
    unfold bridgeCrossingVx
    exact (continuous_id.div_const _).add
      ((contDiff_forwardBridgeCorrection β μ q hq).continuous_deriv (by simp))
  have hiPsi : IntegrableOn (fun x => terminalCrossingPsi β μ q hq m x *
      bridgeCrossingWeight β μ q hq x) (Ioi (0:ℝ)) := by
    apply integrableOn_mul_bridgeCrossingWeight_of_linear_growth β hβ μ q hq _
      (by
        unfold terminalCrossingPsi
        exact ((gaussian_continuous_tanh.mul hcV).add (gaussian_continuous_tanh.pow 2)).sub
          (continuous_const.mul (gaussian_continuous_sech.pow 2)))
      ((β^2*q)⁻¹+2+|1-m|)
      (by have hv := (mul_pos (sq_pos_of_ne_zero hβ) hq.1).le; positivity)
    intro x hx
    have hb : ‖Real.tanh x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
    have hc : ‖sech x ^ 2‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact sech_sq_le_one x
    have hbr : ‖Real.tanh x * bridgeCrossingVx β μ q hq x‖ ≤ |x|/(β^2*q)+1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans
        (by simpa only [one_mul] using bridgeCrossingVx_norm_le β hβ μ q hq x)
    have ht2 : ‖Real.tanh x^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg (Real.tanh x)]
    have hmc : ‖(1-m)*sech x^2‖ ≤ |1-m| := by
      rw [norm_mul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans_eq (mul_one _)
    have hh : ‖terminalCrossingPsi β μ q hq m x‖ ≤ |x|/(β^2*q)+2+|1-m| := by
      calc
        _ ≤ ‖Real.tanh x * bridgeCrossingVx β μ q hq x + Real.tanh x^2‖ +
            ‖(1-m)*sech x^2‖ := norm_sub_le _ _
        _ ≤ (‖Real.tanh x * bridgeCrossingVx β μ q hq x‖ + ‖Real.tanh x^2‖) +
            ‖(1-m)*sech x^2‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by linarith
    apply hh.trans
    rw [div_eq_mul_inv]
    nlinarith [inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hq.1).le,
      abs_nonneg x,abs_nonneg (1-m),
      mul_nonneg (abs_nonneg x) (abs_nonneg (1-m))]
  apply crossing_centered_expectation_from_IBP _ _ _
    (fun x => bridgeCrossingWeight β μ q hq x * backwardZ β μ (q,x))
    (bridgeCrossingWeight_integrable β hβ μ q hq)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ q hq x) hiPhi hiPsi
  · intro x hx
    have hd := hasDerivAt_bridgeCrossingWeight_mul_z β hβ μ q hq x
    convert hd using 1
    change -(terminalCrossingPhi m x + terminalCrossingPsi β μ q hq m x) *
      bridgeCrossingWeight β μ q hq x =
      -(actualCrossingPhi β μ (parisiCDF μ q) (q,x) + bridgeCrossingPsi β μ q hq x) *
      bridgeCrossingWeight β μ q hq x
    change -(terminalCrossingPhi m x + terminalCrossingPsi β μ q hq m x) *
      bridgeCrossingWeight β μ q hq x =
      -(actualCrossingPhi β μ (parisiCDF μ q) (q,x) +
        (backwardZ β μ (q,x)*(bridgeCrossingN β μ q hq x + backwardZ β μ (q,x))-
          (backwardZx β μ (q,x) - parisiCDF μ q * backwardC β μ (q,x)))) *
      bridgeCrossingWeight β μ q hq x
    simp only [actualCrossingPhi,crossingPhi,bridgeCrossingN,
      hcdf,hB x,hC x,hz x,hzder x,
      terminalCrossingPhi,terminalCrossingPsi]
    ring
  · rw [hz 0,Real.tanh_zero,mul_zero]
  · apply tendsto_zero_of_crossingGaussianEnvelope_bound _ (β^2*q) 0
      (Real.exp (β^2)*(Real.sqrt (2*Real.pi*(β^2*q)))⁻¹)
      (mul_pos (sq_pos_of_ne_zero hβ) hq.1)
    intro x hx
    rw [norm_mul,hz x]
    have hb : ‖Real.tanh x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (by simpa only [mul_one] using bridgeCrossingWeight_gaussian_envelope β hβ μ q hq x hx)

end FRSB
