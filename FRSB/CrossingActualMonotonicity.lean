module

public import FRSB.CrossingActualFields
public import FRSB.CrossingMonotonicity
public import FRSB.BackwardsProposition

@[expose] public section

/-! The actual backward fields have the order properties used by the
crossing covariance argument. Every PDE/shape input is discharged here. -/
noncomputable section
open Set Paper
namespace FRSB

theorem actualCrossing_z_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hm : 0 < parisiCDF μ s) (hx : 0 < x) :
    0 < backwardZ β μ (s, x) :=
  (mul_pos hm (backwardB_pos β hβ μ s x hs hx)).trans_le
    (backwardZ_ge_massB β hβ μ s x hs hx.le)

theorem actualCrossingPhi_strictMonoOn (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hm : 0 < parisiCDF μ s) :
    StrictMonoOn (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s, x)) (Ici 0) := by
  apply strictMonoOn_halfLine_of_hasDerivAt_pos _
    (fun x => 2 * backwardZ β μ (s, x) *
      (2 * backwardQ β μ (parisiCDF μ s) (s, x) + 3 * parisiCDF μ s * backwardC β μ (s, x)))
  · exact fun x _ => hasDerivAt_actualCrossingPhi β hβ μ (parisiCDF μ s) s x hs
  · intro x hx
    exact crossingPhi_slope_pos _ _ _ _ hm (backwardC_pos β hβ μ s x hs)
      (actualCrossing_z_pos β hβ μ s x hs hm hx) (backwardQ_nonneg β hβ μ s x hs)

theorem actualCrossingH_monotoneOn (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun x => backwardH β μ (parisiCDF μ s) (s, x)) (Ici 0) := by
  apply crossingH_monotoneOn _ (fun x => backwardHx β μ (parisiCDF μ s) (s, x))
  · exact fun x _ => hasDerivAt_backwardH β hβ μ (parisiCDF μ s) s x hs
  · exact fun x hx => (backwardHx_bounds β hβ μ s x hs hx).1

theorem backwardZ_abs_le_one_halfLine (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    |backwardZ β μ (s, x)| ≤ 1 := by
  have hi := backward_inequalities β hβ μ s x hs hx
  have hn : 0 ≤ backwardZ β μ (s, x) :=
    (mul_nonneg (parisiCDF_nonneg μ s) (backwardB_nonneg β hβ μ s x hs hx)).trans hi.1
  rw [abs_of_nonneg hn]
  exact hi.2.1.trans hi.2.2.1

/-- Bounded logarithmic curvature derivative on the entire spatial line. -/
theorem backwardZ_abs_le_one_crossing (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    |backwardZ β μ (s, x)| ≤ 1 := by
  by_cases hx : 0 ≤ x
  · exact backwardZ_abs_le_one_halfLine β hβ μ s x hs hx
  · have hh := backwardZ_abs_le_one_halfLine β hβ μ s (-x) hs (by linarith)
    simpa only [backwardZ_odd β μ s x hs, abs_neg] using hh

theorem backwardQ_abs_le_one_crossing (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s x : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    |backwardQ β μ (parisiCDF μ s) (s, x)| ≤ 1 := by
  rw [abs_of_nonneg (backwardQ_nonneg β hβ μ s x hs)]
  exact (backwardQ_le β hβ μ s x hs).trans (sub_le_self 1 (parisiCDF_nonneg μ s))

end FRSB
