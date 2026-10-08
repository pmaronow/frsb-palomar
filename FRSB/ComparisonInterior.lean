module

public import FRSB.ComparisonInterval

@[expose] public section

/-! Bounded comparison when differential hypotheses hold only at interior times. -/
noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

theorem interval_supersolution_nonneg_interior (halfLine : Bool)
    (a c K M : ℝ) (hac : a ≤ c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (v vt b κ : ℝ × ℝ → ℝ)
    (hv : ContinuousOn v (Icc a c ×ˢ comparisonSpace halfLine))
    (ht : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      HasDerivAt (fun s => v (s, x)) (vt (t, x)) t)
    (hx : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (fun y => v (t, y)) x)
    (hxx : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (deriv (fun y => v (t, y))) x)
    (hbound : ∀ t ∈ Icc a c, ∀ x ∈ comparisonSpace halfLine, |v (t, x)| ≤ M)
    (hb : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      b (t, x) * sign x ≤ K)
    (hκ : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine, κ (t, x) ≤ K)
    (hPDE : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      0 ≤ vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x))
    (hinitial : ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (a, x))
    (hboundary : halfLine = true → ∀ t ∈ Icc a c, 0 ≤ v (t, 0)) :
    ∀ p ∈ Icc a c ×ˢ comparisonSpace halfLine, 0 ≤ v p := by
  have hi : ∀ t ∈ Ico a c, ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (t, x) := by
    intro t ht0 x hx0
    have hcsub : Icc a t ⊆ Icc a c := fun y hy => ⟨hy.1, hy.2.trans ht0.2.le⟩
    have hosub : Ioc a t ⊆ Ioo a c := fun y hy => ⟨hy.1, hy.2.trans_lt ht0.2⟩
    exact interval_supersolution_nonneg halfLine a t K M ht0.1 hK hM v vt b κ
      (hv.mono (prod_mono hcsub (Subset.refl _)))
      (fun y hy z hz => (ht y (hosub hy) z hz).hasDerivWithinAt)
      (fun y hy z hz => hx y (hosub hy) z hz)
      (fun y hy z hz => hxx y (hosub hy) z hz)
      (fun y hy z hz => hbound y (hcsub hy) z hz)
      (fun y hy z hz => hb y (hosub hy) z hz)
      (fun y hy z hz => hκ y (hosub hy) z hz)
      (fun y hy z hz => hPDE y (hosub hy) z hz)
      hinitial (fun hhalf y hy => hboundary hhalf y (hcsub hy))
      (t, x) ⟨⟨ht0.1, le_rfl⟩, hx0⟩
  intro p hp
  change 0 ≤ v (p.1, p.2)
  by_cases hpc : p.1 < c
  · exact hi p.1 ⟨hp.1.1, hpc⟩ p.2 hp.2
  have hpc : p.1 = c := le_antisymm hp.1.2 (le_of_not_gt hpc)
  by_cases hac' : a < c
  · haveI : NeBot (𝓝[Ioo a c] c) := right_nhdsWithin_Ioo_neBot hac'
    have hcont : ContinuousOn (fun t => v (t, p.2)) (Icc a c) :=
      hv.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht0 => ⟨ht0, hp.2⟩)
    have htend := (hcont c ⟨hac, le_rfl⟩).mono Ioo_subset_Icc_self
    have hlim : 0 ≤ v (c, p.2) := ge_of_tendsto htend.tendsto (by
      filter_upwards [self_mem_nhdsWithin (s := Ioo a c) (a := c)] with t ht0
      exact hi t ⟨ht0.1.le, ht0.2⟩ p.2 hp.2)
    simpa only [← hpc] using hlim
  · have heq : c = a := le_antisymm (le_of_not_gt hac') hac
    simpa only [hpc, heq] using hinitial p.2 hp.2

end FRSB
