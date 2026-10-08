module

public import FRSB.BackwardsDefinitions
public import FRSB.CrossingAlgebra

@[expose] public section

/-! Section 5 fields made from the actual selected Parisi potential, with
 actual spatial derivatives. The forward density has not been replaced by
 an abstract potential here. -/
noncomputable section
open Set
namespace FRSB

def actualCrossingPhi (β : ℝ) (μ : Paper.ParisiMeasure) (m : ℝ) (p : ℝ × ℝ) : ℝ :=
  crossingPhi m (backwardC β μ p) (backwardZ β μ p)

def actualCrossingVelocity (β : ℝ) (μ : Paper.ParisiMeasure) (m : ℝ)
    (p : ℝ × ℝ) : ℝ := m * backwardB β μ p - backwardZ β μ p

theorem hasDerivAt_actualCrossingVelocity (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => actualCrossingVelocity β μ m (t, y))
      (-backwardQ β μ m (t, x)) x := by
  convert ((hasDerivAt_backwardD β μ 1 t x ht).const_mul m).sub
    (hasDerivAt_backwardZ β hβ μ t x ht) using 1
  · funext y; rfl
  · dsimp [backwardQ, backwardQJet, backwardZx, backwardC]
    ring

theorem hasDerivAt_actualCrossingPhi (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => actualCrossingPhi β μ m (t, y))
      (2 * backwardZ β μ (t, x) *
        (2 * backwardQ β μ m (t, x) + 3 * m * backwardC β μ (t, x))) x := by
  apply crossingPhi_hasDerivAt m x (fun y => backwardC β μ (t, y))
    (fun y => backwardZ β μ (t, y)) (fun y => backwardQ β μ m (t, y))
  · rw [← backwardD_three_eq_neg_two_C_z β hβ μ t x ht]
    exact hasDerivAt_backwardD β μ 2 t x ht
  · convert hasDerivAt_backwardZ β hβ μ t x ht using 1
    dsimp [backwardQ, backwardQJet, backwardZx, backwardC]
    ring

/-- The H derivative in the crossing coordinates, now evaluated on the
 genuine Parisi curvature jets. -/
theorem actualCrossing_Hx_identity (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardHx β μ m (t, x) = 2 * backwardZ β μ (t, x) * backwardQ β μ m (t, x) -
      2 * deriv (fun y => backwardQ β μ m (t, y)) x := by
  rw [(hasDerivAt_backwardQ β hβ μ m t x ht).deriv]
  have hC := (backwardC_pos β hβ μ t x ht).ne'
  dsimp [backwardC] at hC
  dsimp [backwardHx, backwardHxJet, backwardQ, backwardQJet, backwardZx, backwardZ,
    backwardZJet, backwardZxJet, backwardQxJet, backwardZxxJet, backwardC]
  field_simp
  ring

/-- The exact Q derivative written in the form used in the Psi derivative. -/
theorem hasDerivAt_backwardQ_crossing_form (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (m t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y => backwardQ β μ m (t, y))
      (backwardZ β μ (t, x) * backwardQ β μ m (t, x) - backwardHx β μ m (t, x) / 2) x := by
  have hd := hasDerivAt_backwardQ β hβ μ m t x ht
  have hh := actualCrossing_Hx_identity β hβ μ m t x ht
  rw [hd.deriv] at hh
  convert hd using 1
  linarith

end FRSB
