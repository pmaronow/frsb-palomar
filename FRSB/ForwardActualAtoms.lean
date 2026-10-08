module

public import FRSB.ForwardAtomBounds
public import FRSB.UniformSpatialRegularity

@[expose] public section

/-! Atom multiplier bounds instantiated with the actual arbitrary-measure PDE. -/
noncomputable section
open Set Paper
open scoped ContDiff
namespace FRSB

def forwardPotentialDerivativeConstant (β : ℝ) (n : ℕ) : ℝ :=
  uniformSpatialConstant β (n - 1)

lemma forwardPotentialDerivativeConstant_pos (β : ℝ) (n : ℕ) :
    0 < forwardPotentialDerivativeConstant β n := uniformSpatialConstant_pos β _

/-- The paper's atom multiplier estimate with no supplied spatial bounds. -/
theorem actual_atom_multiplier_derivative_bound (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Icc (0 : ℝ) 1)
    (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv (j + 1) (fun y => Real.exp (-δ * parisiPotential β μ (s, y))) x‖ ≤
      δ * exponentialDerivativeConstant (forwardPotentialDerivativeConstant β) (j + 1) *
        Real.exp (-δ * parisiPotential β μ (s, x)) := by
  apply norm_iteratedDeriv_exp_neg_mul_le_delta
    (fun y => parisiPotential β μ (s, y)) δ (contDiff_parisiPotential_spatial β μ s hs) hδ
    (forwardPotentialDerivativeConstant β) (fun n => (forwardPotentialDerivativeConstant_pos β n).le)
  intro n y
  rw [← parisiSpatialField_eq_iteratedDeriv β μ (n + 1) s y hs]
  exact parisiSpatialField_uniform_bound β n μ (s, y)

/-- Relative forward-density derivative bounds propagate through every
actual atom by a constant depending only on beta and derivative order. -/
theorem actual_atom_relative_derivative_bound (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (δ : ℝ) (hδ : δ ∈ Icc (0 : ℝ) 1)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hFnon : ∀ x, 0 ≤ F x)
    (L : ℝ) (hL : 0 ≤ L) (k : ℕ)
    (hrelative : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j F x‖ ≤ L * F x)
    (j : ℕ) (hj : j ≤ k) (x : ℝ) :
    ‖iteratedDeriv j (fun y => F y * Real.exp (-δ * parisiPotential β μ (s, y))) x‖ ≤
      (1 + δ * atomDerivativeLoss (forwardPotentialDerivativeConstant β) k) * L *
        (F x * Real.exp (-δ * parisiPotential β μ (s, x))) := by
  apply atom_relative_derivative_bound F (fun y => parisiPotential β μ (s, y)) δ L
    hF (contDiff_parisiPotential_spatial β μ s hs) hδ hL hFnon
    (forwardPotentialDerivativeConstant β) (fun n => (forwardPotentialDerivativeConstant_pos β n).le)
    _ k hrelative j hj x
  intro n y
  rw [← parisiSpatialField_eq_iteratedDeriv β μ (n + 1) s y hs]
  exact parisiSpatialField_uniform_bound β n μ (s, y)

end FRSB
