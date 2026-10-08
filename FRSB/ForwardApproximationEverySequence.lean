module

public import FRSB.ForwardConclusions

@[expose] public section

/-! The forward approximation conclusion for every weak sequence preserving
both paper masses, rather than only the chosen grid construction. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

theorem forward_correction_every_preserving_sequence_cloc
    (β : ℝ) (μ : ParisiMeasure) (ν : ℕ → ParisiMeasure)
    (hν : Tendsto ν atTop (𝓝 μ)) (q : Overlap) (hq : 0 < (q : ℝ))
    (hpreserve : ∀ n, (ν n : Measure Overlap) (Iio q) = (μ : Measure Overlap) (Iio q) ∧
      (ν n : Measure Overlap) {q} = (μ : Measure Overlap) {q})
    (j : ℕ) (S : Set ℝ) (hS : IsCompact S) :
    let hs : (q : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨hq,q.property.2⟩
    TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeCorrection β (ν n) q hs))
      (iteratedDeriv j (forwardBridgeCorrection β μ q hs)) atTop S ∧
    TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeLeftCorrection β (ν n) q hs))
      (iteratedDeriv j (forwardBridgeLeftCorrection β μ q hs)) atTop S := by
  let hs : (q : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨hq,q.property.2⟩
  have hleft : ∀ n, parisiLeftMass (ν n) q = parisiLeftMass μ q := by
    intro n
    unfold parisiLeftMass
    congr 1
    convert (hpreserve n).1 using 1 <;>
      congr 1 <;> ext x <;> simp only [mem_setOf_eq,mem_Iio] <;> rfl
  have hatom : ∀ n, parisiAtomMass (ν n) q hs = parisiAtomMass μ q hs := by
    intro n
    unfold parisiAtomMass
    simpa only using congrArg ENNReal.toReal (hpreserve n).2
  have hα : ∀ n, parisiCDF (ν n) q = parisiCDF μ q := by
    intro n
    rw [parisiCDF_eq_left_add_atom (ν n) q hs,parisiCDF_eq_left_add_atom μ q hs,
      hleft n,hatom n]
  have hαlim : Tendsto (fun n => parisiCDF (ν n) q) atTop (𝓝 (parisiCDF μ q)) := by
    simpa only [hα] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => parisiCDF μ q) atTop (𝓝 (parisiCDF μ q)))
  have hδlim : Tendsto (fun n => parisiAtomMass (ν n) q hs) atTop
      (𝓝 (parisiAtomMass μ q hs)) := by
    simpa only [hatom] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => parisiAtomMass μ q hs) atTop (𝓝 (parisiAtomMass μ q hs)))
  exact ⟨tendstoUniformlyOn_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf
    β μ ν hν q hs hαlim j S hS,
    tendstoUniformlyOn_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses
      β μ ν hν q hs hαlim hδlim j S hS⟩

end FRSB
