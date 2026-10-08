module

public import FRSB.TerminalWeightedMoments
public import FRSB.ForwardBridgeLawLimit

@[expose] public section

/-! Passing actual even terminal moments from the line to the normalized
positive half-line crossing law. -/
noncomputable section
open Set Filter MeasureTheory Paper
namespace FRSB

theorem integral_eq_two_mul_halfLine_of_even (f : ℝ → ℝ)
    (he : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2*(∫ x in Ioi (0:ℝ), f x) := by
  have ha : (fun x : ℝ => f |x|) = f := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx),he x]
  have h := integral_comp_abs (f := f)
  rw [ha] at h
  exact h

theorem bridgeCrossingWeight_even_terminal (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {q : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (x : ℝ) :
    bridgeCrossingWeight β μ q hq (-x) = bridgeCrossingWeight β μ q hq x := by
  have he : ∀ y, backwardC β μ (q,y) = sech y^2 := fun y => by
    rw [backwardC_eq_hessian β μ q y ⟨hq.1.le,hq.2⟩]
    exact parisiHessian_terminal_region β hβ μ ⟨hq.1.le,hq.2⟩ hmax ⟨le_rfl,hq.2⟩ y
  unfold bridgeCrossingWeight
  rw [he (-x),he x,sech_neg,forwardBridgeDensity_even]

theorem terminal_crossing_phi_zero_of_full_moment (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {q : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) (m : ℝ)
    (hmoment : (∫ x, sech x^4 * terminalCrossingPhi m x *
      forwardBridgeDensity β μ q hq x) = 0) :
    (∫ x, terminalCrossingPhi m x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) = 0 := by
  have he : ∀ y, backwardC β μ (q,y) = sech y^2 := fun y => by
    rw [backwardC_eq_hessian β μ q y ⟨hq.1.le,hq.2⟩]
    exact parisiHessian_terminal_region β hβ μ ⟨hq.1.le,hq.2⟩ hmax ⟨le_rfl,hq.2⟩ y
  have hfull : (∫ x, terminalCrossingPhi m x * bridgeCrossingWeight β μ q hq x) = 0 := by
    have hfun : (fun x => terminalCrossingPhi m x * bridgeCrossingWeight β μ q hq x) =
        fun x => 2*(sech x^4 * terminalCrossingPhi m x * forwardBridgeDensity β μ q hq x) := by
      funext x
      unfold bridgeCrossingWeight
      rw [he x]
      ring
    rw [hfun,integral_const_mul,hmoment,mul_zero]
  have hhalf := integral_eq_two_mul_halfLine_of_even
    (fun x => terminalCrossingPhi m x * bridgeCrossingWeight β μ q hq x) (fun x => by
      rw [bridgeCrossingWeight_even_terminal β hβ μ hq hmax x]
      simp only [terminalCrossingPhi,Real.tanh_neg,neg_sq,sech_neg])
  have hz : (∫ x in Ioi (0:ℝ), terminalCrossingPhi m x * bridgeCrossingWeight β μ q hq x) = 0 := by
    rw [hfull] at hhalf
    linarith
  rw [integral_crossingWeightLaw _ _ (bridgeCrossingWeight_integrable β hβ μ q hq)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ q hq x),hz,zero_div]

end FRSB
