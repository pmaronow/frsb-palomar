module

public import FRSB.BackwardsProposition

@[expose] public section

noncomputable section
open Set
namespace FRSB

theorem backwardZ_abs_le_one (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |backwardZ β μ (t,x)| ≤ 1 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg (backwardZ_nonneg β hβ μ t x ht hx)]
    exact backwardZ_le_one β hβ μ t x ht hx
  · have hn : 0 ≤ -x := by linarith
    have hh : |backwardZ β μ (t,-x)| ≤ 1 := by
      rw [abs_of_nonneg (backwardZ_nonneg β hβ μ t (-x) ht hn)]
      exact backwardZ_le_one β hβ μ t (-x) ht hn
    simpa only [backwardZ_odd β μ t x ht,abs_neg] using hh

theorem backwardHx_abs_le (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |backwardHx β μ (Paper.parisiCDF μ t) (t,x)| ≤ 6*(1-Paper.parisiCDF μ t) := by
  by_cases hx : 0 ≤ x
  · have hh := backwardHx_bounds β hβ μ t x ht hx
    rw [abs_of_nonneg hh.1]
    exact hh.2
  · have hn : 0 ≤ -x := by linarith
    have hh := backwardHx_bounds β hβ μ t (-x) ht hn
    have hb : |backwardHx β μ (Paper.parisiCDF μ t) (t,-x)| ≤ 6*(1-Paper.parisiCDF μ t) := by
      rw [abs_of_nonneg hh.1]
      exact hh.2
    simpa only [backwardHx_odd β μ (Paper.parisiCDF μ t) t x ht,abs_neg] using hb

/-- Proposition 3.1's full-line boundedness conclusion, with explicit
universal bounds for the actual five fields. -/
theorem backward_fields_bounded (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |backwardZ β μ (t,x)| ≤ 1 ∧ |backwardQ β μ (Paper.parisiCDF μ t) (t,x)| ≤ 1 ∧
    |backwardH β μ (Paper.parisiCDF μ t) (t,x)| ≤ 2 ∧
    |backwardHx β μ (Paper.parisiCDF μ t) (t,x)| ≤ 6 ∧
    |backwardC β μ (t,x)*backwardHx β μ (Paper.parisiCDF μ t) (t,x)| ≤ 6 := by
  have hz := backwardZ_abs_le_one β hβ μ t x ht
  have hq0 := backwardQ_nonneg β hβ μ t x ht
  have hq1 : backwardQ β μ (Paper.parisiCDF μ t) (t,x) ≤ 1 :=
    (backwardQ_le β hβ μ t x ht).trans (by linarith [Paper.parisiCDF_nonneg μ t])
  have hc0 := (backwardC_pos β hβ μ t x ht).le
  have hc1 := backwardC_le_one β hβ μ t x ht
  have ha0 := Paper.parisiCDF_nonneg μ t
  have ha1 := Paper.parisiCDF_le_one μ t
  have hac : 0 ≤ Paper.parisiCDF μ t*backwardC β μ (t,x) := mul_nonneg ha0 hc0
  have hac1 : Paper.parisiCDF μ t*backwardC β μ (t,x) ≤ 1 := mul_le_one₀ ha1 hc0 hc1
  have hx6 : |backwardHx β μ (Paper.parisiCDF μ t) (t,x)| ≤ 6 :=
    (backwardHx_abs_le β hβ μ t x ht).trans (by nlinarith [ha0])
  refine ⟨hz,by rwa [abs_of_nonneg hq0],?_,hx6,?_⟩
  · rw [backwardH_eq_z_sq_mC_sub_twoQ,abs_le]
    have hzsq : backwardZ β μ (t,x)^2 ≤ 1 := by nlinarith [abs_le.mp hz]
    constructor <;> nlinarith [sq_nonneg (backwardZ β μ (t,x))]
  · rw [abs_mul,abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left hx6 hc0).trans (by nlinarith)

end FRSB
