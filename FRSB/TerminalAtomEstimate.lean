module

public import FRSB.TerminalPhysicalMoment
public import FRSB.ForwardLeftPotential
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The actual terminal atom estimate from the two remaining geometric
inputs: the forward left-gauge shape and the identified quotient centering. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff
namespace FRSB

theorem forwardLeftPotential_deriv_eq_score (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) (x : ℝ) :
    deriv (forwardLeftPotential β μ s hs) x = bridgeCrossingVx β μ s hs x -
      (parisiCDF μ s-parisiLeftMass μ s)*backwardB β μ (s,x) := by
  have hd := ((hasDerivAt_parisiPotential_spatial_all β μ s x ⟨hs.1.le,hs.2⟩).const_mul
    (parisiLeftMass μ s)).sub
    ((hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x).log
      (forwardBridgeDensity_pos β hβ μ s hs x).ne')
  have hf : (fun y => parisiLeftMass μ s * parisiPotential β μ (s,y)-
      Real.log (forwardBridgeDensity β μ s hs y)) = forwardLeftPotential β μ s hs := rfl
  change HasDerivAt (forwardLeftPotential β μ s hs) _ x at hd
  rw [hd.deriv,backwardB_eq_gradient β μ s x ⟨hs.1.le,hs.2⟩]
  field_simp [(forwardBridgeDensity_pos β hβ μ s hs x).ne']
  ring

theorem terminal_atom_quadratic_of_shape_and_centering (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ q hq) x ≤ 0)
    (hphi : (∫ x, terminalCrossingPhi (parisiLeftMass μ q) x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) = 0) :
    parisiLeftMass μ q * (4-parisiLeftMass μ q+1/(β^2*q)) ≤ 2 := by
  let m := parisiLeftMass μ q
  let P := crossingWeightLaw (bridgeCrossingWeight β μ q hq)
  let R := deriv (forwardLeftPotential β μ q hq)
  have hm : ∀ x, R x = bridgeCrossingVx β μ q hq x-(1-m)*Real.tanh x := by
    intro x
    dsimp only [R]
    rw [forwardLeftPotential_deriv_eq_score β hβ μ q hq x,
      parisiCDF_eq_one_above_support μ hmax le_rfl,
      backwardB_eq_gradient β μ q x ⟨hq.1.le,hq.2⟩,
      parisiGradient_terminal_region β hβ μ ⟨hq.1.le,hq.2⟩ hmax ⟨le_rfl,hq.2⟩]
  have hBR : Integrable (fun x => Real.tanh x*R x) P := by
    apply integrable_crossingWeightLaw_of_weighted _ _
      (bridgeCrossingWeight_integrable β hβ μ q hq)
      (fun x _ => bridgeCrossingWeight_pos β hβ μ q hq x)
    apply integrableOn_mul_bridgeCrossingWeight_of_linear_growth β hβ μ q hq _
      (gaussian_continuous_tanh.mul ((contDiff_forwardLeftPotential β hβ μ q hq).continuous_deriv (by simp)))
      ((β^2*q)⁻¹+1+|1-m|)
      (by have hv := (mul_pos (sq_pos_of_ne_zero hβ) hq.1).le; positivity)
    intro x hx
    have hb : ‖Real.tanh x‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
    have ht : ‖(1-m)*Real.tanh x‖ ≤ |1-m| := by
      rw [norm_mul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _)
    have hR : ‖R x‖ ≤ |x|/(β^2*q)+1+|1-m| := by
      rw [hm x]
      exact (norm_sub_le _ _).trans
        (add_le_add (bridgeCrossingVx_norm_le β hβ μ q hq x) ht)
    have hBR : ‖Real.tanh x*R x‖ ≤ |x|/(β^2*q)+1+|1-m| := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans (by simpa only [one_mul] using hR)
    apply hBR.trans
    rw [div_eq_mul_inv]
    nlinarith [inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hq.1).le,
      abs_nonneg x,abs_nonneg (1-m),mul_nonneg (abs_nonneg x) (abs_nonneg (1-m))]
  apply terminal_atom_inequality_of_integrals P Real.tanh (fun x => sech x^2) R m (1/(β^2*q))
    (integrable_terminal_crossing_B2 β hβ μ q hq)
    (integrable_terminal_crossing_C β hβ μ q hq) hBR
    (terminal_crossing_C_integral_pos β hβ μ q hq) hphi
  · have hp := terminal_crossing_centering β hβ μ hq hmax m
    rw [hphi,neg_zero] at hp
    convert hp using 1
    congr 1
    funext x
    rw [hm x]
    unfold terminalCrossingPsi
    ring
  · filter_upwards [crossingWeightLaw_halfLine (bridgeCrossingWeight β μ q hq)] with x hx
    have hc := contDiff_forwardLeftPotential β hβ μ q hq
    have hd : ∀ y, HasDerivAt R (iteratedDeriv 2 (forwardLeftPotential β μ q hq) y) y := by
      intro y
      have hdc : ContDiff ℝ ∞ (deriv (forwardLeftPotential β μ q hq)) :=
        (contDiff_infty_iff_deriv.mp hc).2
      have he := hdc.differentiable (by simp) y |>.hasDerivAt
      convert he using 1
      rw [show (2:ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
    have hr := tanh_lower_bound_of_curvature R
      (iteratedDeriv 2 (forwardLeftPotential β μ q hq)) (1/(β^2*q))
      (by have hv := mul_pos (sq_pos_of_ne_zero hβ) hq.1; positivity) hd
      (forwardLeftPotential_curvature_lower_of_third β hβ μ q hq hshape)
      (forwardLeftPotential_deriv_origin β μ q hq) hx
    calc
      1/(β^2*q)*Real.tanh x^2 = Real.tanh x*(1/(β^2*q)*Real.tanh x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (tanh_nonneg_on_halfLine hx)

end FRSB
