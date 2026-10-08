module

public import FRSB.AtomAlgebra
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! The moment elimination leading to the quantitative terminal atom bound. -/
open MeasureTheory
namespace FRSB

theorem terminal_atom_inequality_of_moments {m ell b₂ c r : ℝ}
    (hc : 0 < c) (hphi : 2 * b₂ = m * c)
    (hpsi : r + (2 - m) * b₂ - (1 - m) * c = 0)
    (hr : ell * b₂ ≤ r) : m * (4 - m + ell) ≤ 2 := by
  have heq : (m * (4 - m + ell) - 2) * c = 2 * (ell * b₂ - r) := by
    linear_combination -(2 - m + ell) * hphi + 2 * hpsi
  have hscaled : (m * (4 - m + ell) - 2) * c ≤ 0 := by rw [heq]; linarith
  by_contra h
  have hp : 0 < (m * (4 - m + ell) - 2) * c := mul_pos (by linarith) hc
  linarith

theorem terminal_atom_inequality_of_integrals {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B C R : Ω → ℝ) (m ell : ℝ)
    (hB2 : Integrable (fun x => B x ^ 2) P)
    (hC : Integrable C P) (hBR : Integrable (fun x => B x * R x) P)
    (hCpos : 0 < ∫ x, C x ∂P)
    (hphi : (∫ x, 2 * B x ^ 2 - m * C x ∂P) = 0)
    (hpsi : (∫ x, B x * R x + (2 - m) * B x ^ 2 - (1 - m) * C x ∂P) = 0)
    (hR : ∀ᵐ x ∂P, ell * B x ^ 2 ≤ B x * R x) :
    m * (4 - m + ell) ≤ 2 := by
  have hp : 2 * (∫ x, B x ^ 2 ∂P) = m * ∫ x, C x ∂P := by
    rw [integral_sub (hB2.const_mul 2) (hC.const_mul m),
      integral_const_mul, integral_const_mul] at hphi
    linarith
  have hs : (∫ x, B x * R x ∂P) + (2 - m) * (∫ x, B x ^ 2 ∂P) -
      (1 - m) * (∫ x, C x ∂P) = 0 := by
    change (∫ x, (((fun x : Ω => B x * R x) + (fun x : Ω => (2 - m) * B x ^ 2)) : Ω → ℝ) x -
      (fun x : Ω => (1 - m) * C x) x ∂P) = 0 at hpsi
    rw [integral_sub (hBR.add (hB2.const_mul _)) (hC.const_mul _)] at hpsi
    simp only [Pi.add_apply] at hpsi
    rw [integral_add hBR (hB2.const_mul _), integral_const_mul, integral_const_mul] at hpsi
    exact hpsi
  have hr : ell * (∫ x, B x ^ 2 ∂P) ≤ ∫ x, B x * R x ∂P := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hB2.const_mul ell) hBR hR
  exact terminal_atom_inequality_of_moments hCpos hp hs hr

end FRSB
