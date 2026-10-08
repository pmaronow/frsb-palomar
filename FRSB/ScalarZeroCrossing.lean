module

public import FRSB.CrossingShape
public import Mathlib.Analysis.Calculus.DerivativeTest

@[expose] public section

/-! A positive derivative at every zero forces a single upward sign crossing.
This permits the support argument to use the actual third-derivative identity
without requiring a choice of an integrating-factor coefficient. -/

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem positive_right_of_positive_derivative_at_zero
    (f : ℝ → ℝ) {x y d : ℝ} (hxy : x < y)
    (hd : HasDerivAt f d x) (hdpos : 0 < d) (hx : f x = 0) :
    ∃ z ∈ Ioo x y, 0 < f z := by
  have he : ∀ᶠ z in 𝓝[>] x, 0 < slope f x z :=
    (hasDerivAt_iff_tendsto_slope.mp hd).eventually
      (eventually_gt_nhds hdpos) |>.filter_mono
        (nhdsGT_le_nhdsNE x)
  have hy : ∀ᶠ z in 𝓝[>] x, z < y :=
    (eventually_lt_nhds hxy).filter_mono nhdsWithin_le_nhds
  obtain ⟨z, ⟨hz, hzy⟩, hzx⟩ := (he.and hy |>.and self_mem_nhdsWithin).exists
  exact ⟨z, ⟨hzx, hzy⟩, pos_of_slope_pos hzx hz hx⟩

theorem negative_left_of_positive_derivative_at_zero
    (f : ℝ → ℝ) {x y d : ℝ} (hxy : x < y)
    (hd : HasDerivAt f d y) (hdpos : 0 < d) (hy : f y = 0) :
    ∃ z ∈ Ioo x y, f z < 0 := by
  have he : ∀ᶠ z in 𝓝[<] y, 0 < slope f y z :=
    (hasDerivAt_iff_tendsto_slope.mp hd).eventually
      (eventually_gt_nhds hdpos) |>.filter_mono
        (nhdsLT_le_nhdsNE y)
  have hx : ∀ᶠ z in 𝓝[<] y, x < z :=
    (eventually_gt_nhds hxy).filter_mono nhdsWithin_le_nhds
  obtain ⟨z, ⟨hz, hxz⟩, hzy⟩ := (he.and hx |>.and self_mem_nhdsWithin).exists
  exact ⟨z, ⟨hxz, hzy⟩, neg_of_slope_pos hzy hz hy⟩

theorem positive_derivative_at_zeros_preserves_positive
    (f df : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Ioo a b, f x = 0 → 0 < df x)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hxy : x < y) (hfx : 0 < f x) : 0 < f y := by
  by_contra hfy
  have hfy : f y ≤ 0 := le_of_not_gt hfy
  have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
    ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
  obtain ⟨w, hw, hw0⟩ :=
    intermediate_value_Icc' hxy.le (hc.mono hsub) ⟨hfy, hfx.le⟩
  let S : Set ℝ := Icc x y ∩ f ⁻¹' ({0} : Set ℝ)
  have hclosed : IsClosed S := (hc.mono hsub).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_singleton
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨c, hcS, hleast⟩ := hS.exists_isLeast ⟨w, hw, hw0⟩
  have hc0 : f c = 0 := hcS.2
  have hxc : x < c := lt_of_le_of_ne hcS.1.1 (by
    intro he
    subst c
    linarith)
  obtain ⟨z, hz, hfz⟩ := negative_left_of_positive_derivative_at_zero f hxc
    (hd c (hsub hcS.1)) (hp c (hsub hcS.1) hc0) hc0
  have hsubz : Icc x z ⊆ Ioo a b := fun t ht =>
    hsub ⟨ht.1, ht.2.trans (hz.2.le.trans hcS.1.2)⟩
  obtain ⟨d, hdI, hd0⟩ := intermediate_value_Icc' hz.1.le
    (hc.mono hsubz) ⟨hfz.le, hfx.le⟩
  have hcd : c ≤ d := hleast ⟨⟨hdI.1, hdI.2.trans (hz.2.le.trans hcS.1.2)⟩, hd0⟩
  exact (not_lt_of_ge hcd) (hdI.2.trans_lt hz.2)

theorem nonnegative_derivative_zero_crossing_preserves_positive
    (f df : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Ioo a b, f x = 0 → 0 < df x)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    (hxy : x < y) (hfx : 0 ≤ f x) : 0 < f y := by
  rcases hfx.eq_or_lt with hfx | hfx
  · obtain ⟨z, hz, hfz⟩ := positive_right_of_positive_derivative_at_zero f hxy
      (hd x hx) (hp x hx hfx.symm) hfx.symm
    exact positive_derivative_at_zeros_preserves_positive f df a b hc hd hp
      ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩ hy hz.2 hfz
  · exact positive_derivative_at_zeros_preserves_positive f df a b hc hd hp hx hy hxy hfx

theorem positive_derivative_at_zeros_sign_threshold
    (f df : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hc : ContinuousOn f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Ioo a b, f x = 0 → 0 < df x) :
    ∃ c ∈ Icc a b,
      (∀ x ∈ Ioo a c, f x < 0) ∧ (∀ x ∈ Ioo c b, 0 < f x) := by
  classical
  by_cases hn : ∀ x ∈ Ioo a b, f x < 0
  · exact ⟨b, ⟨hab.le, le_rfl⟩, hn, fun x hx => (lt_irrefl b (hx.1.trans hx.2)).elim⟩
  by_cases hpall : ∀ x ∈ Ioo a b, 0 < f x
  · exact ⟨a, ⟨le_rfl, hab.le⟩,
      fun x hx => (lt_irrefl a (hx.1.trans hx.2)).elim, hpall⟩
  push Not at hn hpall
  obtain ⟨x, hx, hfx⟩ := hn
  obtain ⟨y, hy, hfy⟩ := hpall
  have hz : ∃ c ∈ Ioo a b, f c = 0 := by
    by_cases hx0 : f x = 0
    · exact ⟨x, hx, hx0⟩
    by_cases hy0 : f y = 0
    · exact ⟨y, hy, hy0⟩
    have hyx : y < x := by
      by_contra h
      have hxy : x ≤ y := le_of_not_gt h
      rcases hxy.eq_or_lt with rfl | hxy
      · exact hx0 (le_antisymm hfy hfx)
      · have := nonnegative_derivative_zero_crossing_preserves_positive
          f df a b hc hd hp hx hy hxy hfx
        linarith
    have hsub : Icc y x ⊆ Ioo a b := fun z hz =>
      ⟨hy.1.trans_le hz.1, hz.2.trans_lt hx.2⟩
    obtain ⟨c, hcI, hc0⟩ := intermediate_value_Icc hyx.le (hc.mono hsub) ⟨hfy, hfx⟩
    exact ⟨c, hsub hcI, hc0⟩
  obtain ⟨c, hcI, hc0⟩ := hz
  refine ⟨c, ⟨hcI.1.le, hcI.2.le⟩, ?_, ?_⟩
  · intro x hx
    by_contra h
    have := nonnegative_derivative_zero_crossing_preserves_positive f df a b hc hd hp
      ⟨hx.1, hx.2.trans hcI.2⟩ hcI hx.2 (le_of_not_gt h)
    linarith
  · intro x hx
    exact nonnegative_derivative_zero_crossing_preserves_positive f df a b hc hd hp
      hcI ⟨hcI.1.trans hx.1, hx.2⟩ hx.1 hc0.ge

theorem crossing_shape_of_positive_derivative_at_zeros
    (G f df : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hG : ∀ x ∈ Ioo a b, HasDerivAt G (f x) x)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Ioo a b, f x = 0 → 0 < df x) :
    ∃ c ∈ Icc a b,
      StrictAntiOn G (Ioc a c ∩ Ioo a b) ∧
      StrictMonoOn G (Ico c b ∩ Ioo a b) := by
  have hc : ContinuousOn f (Ioo a b) := fun x hx =>
    (hf x hx).continuousAt.continuousWithinAt
  obtain ⟨c, hcI, hn, hpall⟩ :=
    positive_derivative_at_zeros_sign_threshold f df a b hab hc hf hp
  refine ⟨c, hcI, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg ((convex_Ioc a c).inter (convex_Ioo a b))
    · exact fun x hx => (hG x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have hxmem : x ∈ Ioc a c ∩ Ioo a b := interior_subset hx
      have hi : x ∈ interior (Ioc a c) := interior_mono inter_subset_left hx
      have hxc : x < c := (by simpa only [interior_Ioc, mem_Ioo] using hi : a < x ∧ x < c).2
      rw [(hG x hxmem.2).deriv]
      exact hn x ⟨hxmem.2.1, hxc⟩
  · apply strictMonoOn_of_deriv_pos ((convex_Ico c b).inter (convex_Ioo a b))
    · exact fun x hx => (hG x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have hxmem : x ∈ Ico c b ∩ Ioo a b := interior_subset hx
      have hi : x ∈ interior (Ico c b) := interior_mono inter_subset_left hx
      have hcx : c < x := (by simpa only [interior_Ico, mem_Ioo] using hi : c < x ∧ x < b).1
      rw [(hG x hxmem.2).deriv]
      exact hpall x ⟨hcx, hxmem.2.2⟩

end FRSB
