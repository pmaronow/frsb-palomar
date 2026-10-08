module

public import FRSB.BackwardsBounded
public import FRSB.ForwardLeftAtoms

@[expose] public section

/-! Literal backward jumps at the atoms of the actual probability measure.
The pre-atom coefficient is the genuine mass of Iio t. -/
noncomputable section
open Set Paper
namespace FRSB

theorem backward_actual_atom_updates (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    backwardC β μ (t,x) * backwardQ β μ (parisiLeftMass μ t) (t,x) =
      backwardC β μ (t,x) * backwardQ β μ (parisiCDF μ t) (t,x) +
        parisiAtomMass μ t ht * backwardC β μ (t,x)^2 ∧
    backwardC β μ (t,x) * backwardHx β μ (parisiLeftMass μ t) (t,x) =
      backwardC β μ (t,x) * backwardHx β μ (parisiCDF μ t) (t,x) +
        6 * parisiAtomMass μ t ht * backwardC β μ (t,x)^2 * backwardZ β μ (t,x) := by
  have hm : parisiCDF μ t - parisiAtomMass μ t ht = parisiLeftMass μ t := by
    rw [parisiCDF_eq_left_add_atom μ t ht]
    ring
  have hh := backward_atom_updates (parisiCDF μ t) (parisiAtomMass μ t ht)
    (backwardC β μ (t,x)) (backwardD β μ 3 (t,x))
    (backwardD β μ 4 (t,x)) (backwardD β μ 5 (t,x))
    (backwardC_pos β hβ μ t x ⟨ht.1.le,ht.2⟩).ne'
  rw [hm] at hh
  exact ⟨hh.1,hh.2.2⟩

theorem backward_actual_atom_increments_nonneg (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1)
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ parisiAtomMass μ t ht * backwardC β μ (t,x)^2 ∧
    0 ≤ parisiAtomMass μ t ht * backwardC β μ (t,x) * (1-backwardC β μ (t,x)) ∧
    0 ≤ parisiAtomMass μ t ht * (1-backwardB β μ (t,x)) ∧
    0 ≤ 6 * parisiAtomMass μ t ht * backwardC β μ (t,x)^2 * backwardZ β μ (t,x) ∧
    0 ≤ 6 * parisiAtomMass μ t ht * backwardC β μ (t,x) *
      (1-backwardC β μ (t,x)*backwardZ β μ (t,x)) := by
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2⟩
  apply backward_atom_increments_nonneg _ _ _ _ (parisiAtomMass_nonneg μ t ht)
  · rw [backwardB_eq_gradient β μ t x htc]
    exact le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using norm_parisiGradient_le_one β μ (t,x))
  · exact (backwardC_pos β hβ μ t x htc).le
  · exact backwardC_le_one β hβ μ t x htc
  · exact backwardZ_nonneg β hβ μ t x htc hx
  · exact backwardZ_le_one β hβ μ t x htc hx

end FRSB
