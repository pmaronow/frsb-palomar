module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! The endpoint calculus contradiction at a putative positive support
minimum. Its inputs are later instantiated with the actual Gamma evolution. -/
open Set MeasureTheory
namespace FRSB

theorem no_positive_first_endpoint (F g : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    (hF : ContinuousOn F (Icc 0 a)) (hg : ContinuousOn g (Icc 0 a))
    (hdF : ∀ s ∈ Ioo 0 a, HasDerivAt F (g s) s)
    (hdg : ∀ s ∈ Ioo 0 a, 0 < deriv g s)
    (hF0 : F 0 = 0) (hFa : F a = a) (hga : g a ≤ 1) : False := by
  have hm : StrictMonoOn g (Icc 0 a) :=
    strictMonoOn_of_deriv_pos (convex_Icc 0 a) hg (by
      simpa only [interior_Icc] using hdg)
  have hle : ∀ s ∈ Ioc 0 a, g s ≤ 1 := by
    intro s hs
    exact (hm.monotoneOn ⟨hs.1.le, hs.2⟩ ⟨ha.le, le_rfl⟩ hs.2).trans hga
  have hlt : ∃ s ∈ Icc 0 a, g s < 1 :=
    ⟨0, ⟨le_rfl, ha.le⟩, (hm ⟨le_rfl, ha.le⟩ ⟨ha.le, le_rfl⟩ ha).trans_le hga⟩
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    ha hg continuousOn_const hle hlt
  have hgi : IntervalIntegrable g volume 0 a := hg.intervalIntegrable_of_Icc ha.le
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le hF hdF hgi
  rw [he, hF0, hFa, sub_zero, intervalIntegral.integral_const] at hi
  simp at hi

end FRSB
