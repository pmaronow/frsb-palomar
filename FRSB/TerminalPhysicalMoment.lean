module

public import FRSB.TerminalHalfLine
public import FRSB.SupportQuotient

@[expose] public section

/-! The actual minimizing diffusion's terminal quotient centering, before
transferring it to the identified forward density. -/
noncomputable section
open Set MeasureTheory Paper
namespace FRSB

theorem terminal_physical_phi_moment_zero (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0:ℝ) q) :
    (∫ sample, sech (optimalStateReal β μ sample q)^4 *
      terminalCrossingPhi (((μ : Measure Overlap) {x | (x:ℝ) < q}).toReal)
        (optimalStateReal β μ sample q) ∂canonicalBrownianMeasure) = 0 := by
  let m := ((μ : Measure Overlap) {x | (x:ℝ) < q}).toReal
  have hmax : ∀ x ∈ parisiSupport μ, x ≤ q := fun x hx => (hsupp ▸ hx).2
  have hc : ∀ sample, C β μ q sample = sech (optimalStateReal β μ sample q)^2 := by
    intro sample
    rw [C_eq_hessian]
    exact parisiHessian_terminal_region β hβ μ ⟨hq.le,hq1⟩ hmax ⟨le_rfl,hq1⟩ _
  have hd : ∀ sample, D β μ q sample =
      -2*Real.tanh (optimalStateReal β μ sample q)*sech (optimalStateReal β μ sample q)^2 := by
    intro sample
    exact parisiSpatialJet_three_terminal_region β hβ μ ⟨hq.le,hq1⟩ hmax ⟨le_rfl,hq1⟩ _
  have hfun : (fun sample => sech (optimalStateReal β μ sample q)^4 *
      terminalCrossingPhi m (optimalStateReal β μ sample q)) =
      fun sample => D β μ q sample^2/2 - m*C β μ q sample^3 := by
    funext sample
    rw [hc sample,hd sample]
    unfold terminalCrossingPhi
    ring
  have hm : quotientNumerator β μ q = m*(2*quotientDenominator β μ q) := by
    have he := (momentQuotient_terminal_mass_of_support_interval β hβ μ hmin q hq hq1 hsupp).symm
    change quotientNumerator β μ q/(2*quotientDenominator β μ q) = m at he
    exact (div_eq_iff (mul_ne_zero (by norm_num) (quotientDenominator_pos β hβ μ q ⟨hq.le,hq1⟩).ne')).mp he
  rw [hfun,integral_sub ((integrable_jetProcess_pow β hβ μ 2 2 ⟨hq.le,hq1⟩).div_const 2)
    ((integrable_jetProcess_pow β hβ μ 1 3 ⟨hq.le,hq1⟩).const_mul m),
    integral_div,integral_const_mul]
  rw [← moment_X_pow β μ 2 2 q,← moment_X_pow β μ 1 3 q]
  change quotientNumerator β μ q/2-m*quotientDenominator β μ q = 0
  rw [hm]
  ring

end FRSB
