module

public import FRSB.QuotientContinuity

@[expose] public section

/-! A constant overlap CDF on an open interval has the same value at
the left endpoint. This translates the paper's open-interval hypotheses
to the half-open cell convention used by the finite-grid calculus. -/
noncomputable section
open Set Filter Paper
open scoped Topology
namespace FRSB

theorem parisiCDF_constant_Ico_of_Ioo (μ : ParisiMeasure) {a b m : ℝ}
    (hab : a < b) (hc : ∀ s ∈ Ioo a b, parisiCDF μ s = m) :
    ∀ s ∈ Ico a b, parisiCDF μ s = m := by
  have he : ∀ᶠ s in 𝓝[>] a, parisiCDF μ s = m := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)] with s hs hs'
    exact hc s ⟨hs,hs'⟩
  have hlim : Tendsto (parisiCDF μ) (𝓝[>] a) (𝓝 m) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with s hs using hs.symm
  have ha : parisiCDF μ a = m :=
    tendsto_nhds_unique ((parisiCDF_continuousWithinAt_right μ a).mono
      Ioi_subset_Ici_self) hlim
  intro s hs
  rcases eq_or_lt_of_le hs.1 with rfl | hsa
  · exact ha
  · exact hc s ⟨hsa,hs.2⟩

end FRSB
