module

public import FRSB.CrossingMonotonicity

@[expose] public section

/-! The global sign shape of the crossing representation. A continuous,
strictly increasing integrating factor has at most one zero, and its sign
changes from negative to positive. The crossing PDE still has to supply
that integrating factor and its strict derivative. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB

/-- A strictly increasing continuous function on a nonempty bounded open
 interval changes sign at a threshold in its closure. The endpoint cases
 include functions with a constant strict sign throughout the interval. -/
theorem strictMonoOn_sign_threshold (g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hc : ContinuousOn g (Ioo a b)) (hm : StrictMonoOn g (Ioo a b)) :
    ∃ c ∈ Icc a b,
      (∀ x ∈ Ioo a c, g x < 0) ∧ (∀ x ∈ Ioo c b, 0 < g x) := by
  classical
  by_cases hn : ∀ x ∈ Ioo a b, g x < 0
  · refine ⟨b, ⟨hab.le, le_rfl⟩, hn, ?_⟩
    intro x hx
    exact False.elim (not_lt_of_ge hx.1.le hx.2)
  by_cases hp : ∀ x ∈ Ioo a b, 0 < g x
  · refine ⟨a, ⟨le_rfl, hab.le⟩, ?_, hp⟩
    intro x hx
    exact False.elim (not_lt_of_ge hx.1.le hx.2)
  push Not at hn hp
  obtain ⟨x, hx, hxg⟩ := hn
  obtain ⟨y, hy, hyg⟩ := hp
  have hz : ∃ c ∈ Ioo a b, g c = 0 := by
    by_cases hx0 : g x = 0
    · exact ⟨x, hx, hx0⟩
    by_cases hy0 : g y = 0
    · exact ⟨y, hy, hy0⟩
    have hyx : y < x := by
      by_contra h
      have hxy : x ≤ y := le_of_not_gt h
      have hmon := hm.monotoneOn hx hy hxy
      have hxpos : 0 < g x := lt_of_le_of_ne hxg (Ne.symm hx0)
      linarith
    have hsub : Icc y x ⊆ Ioo a b := by
      intro z hz
      exact ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
    obtain ⟨c, hcyx, hc0⟩ := intermediate_value_Icc hyx.le (hc.mono hsub) ⟨hyg, hxg⟩
    exact ⟨c, hsub hcyx, hc0⟩
  obtain ⟨c, hcI, hc0⟩ := hz
  refine ⟨c, ⟨hcI.1.le, hcI.2.le⟩, ?_, ?_⟩
  · intro z hz
    have hzI : z ∈ Ioo a b := ⟨hz.1, hz.2.trans hcI.2⟩
    simpa only [hc0] using hm hzI hcI hz.2
  · intro z hz
    have hzI : z ∈ Ioo a b := ⟨hcI.1.trans hz.1, hz.2⟩
    simpa only [hc0] using hm hcI hzI hz.1

/-- The sign threshold of a positive integrating factor produces the
 decreasing-then-increasing shape of the differentiated Gamma function. -/
theorem crossing_shape_of_positive_factor
    (G dG g w : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hG : ∀ x ∈ Ioo a b, HasDerivAt G (dG x) x)
    (hg : ContinuousOn g (Ioo a b)) (hmono : StrictMonoOn g (Ioo a b))
    (hw : ∀ x ∈ Ioo a b, 0 < w x)
    (hfactor : ∀ x ∈ Ioo a b, dG x = w x * g x) :
    ∃ c ∈ Icc a b,
      StrictAntiOn G (Ioc a c ∩ Ioo a b) ∧
      StrictMonoOn G (Ico c b ∩ Ioo a b) := by
  obtain ⟨c, hc, hn, hp⟩ := strictMonoOn_sign_threshold g a b hab hg hmono
  refine ⟨c, hc, ?_, ?_⟩
  · apply strictAntiOn_of_deriv_neg ((convex_Ioc a c).inter (convex_Ioo a b))
    · intro x hx
      exact (hG x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have hxmem : x ∈ Ioc a c ∩ Ioo a b := interior_subset hx
      have hxc : x < c := by
        have hi : x ∈ interior (Ioc a c) := interior_mono inter_subset_left hx
        exact (by simpa only [interior_Ioc, mem_Ioo] using hi : a < x ∧ x < c).2
      rw [(hG x hxmem.2).deriv, hfactor x hxmem.2]
      exact mul_neg_of_pos_of_neg (hw x hxmem.2) (hn x ⟨hxmem.2.1, hxc⟩)
  · apply strictMonoOn_of_deriv_pos ((convex_Ico c b).inter (convex_Ioo a b))
    · intro x hx
      exact (hG x hx.2).continuousAt.continuousWithinAt
    · intro x hx
      have hxmem : x ∈ Ico c b ∩ Ioo a b := interior_subset hx
      have hcx : c < x := by
        have hi : x ∈ interior (Ico c b) := interior_mono inter_subset_left hx
        exact (by simpa only [interior_Ico, mem_Ioo] using hi : c < x ∧ x < b).1
      rw [(hG x hxmem.2).deriv, hfactor x hxmem.2]
      exact mul_pos (hw x hxmem.2) (hp x ⟨hcx, hxmem.2.2⟩)

/-- The exact integrating factor from the paper, proved using the FTC on
 the open interval where the averaged transport coefficient is continuous. -/
theorem hasDerivAt_crossing_integrating_factor (f f' q : ℝ → ℝ)
    (a b t₀ t : ℝ) (ht₀ : t₀ ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hq : ContinuousOn q (Ioo a b)) (hf : HasDerivAt f (f' t) t) :
    HasDerivAt (fun r => Real.exp (-(∫ u in t₀..r, q u)) * f r)
      (Real.exp (-(∫ u in t₀..t, q u)) * (f' t - q t * f t)) t := by
  have hsub : uIcc t₀ t ⊆ Ioo a b := by
    rw [uIcc]
    intro r hr
    exact ⟨lt_min ht₀.1 ht.1 |>.trans_le hr.1,
      hr.2.trans_lt (max_lt ht₀.2 ht.2)⟩
  have hi : HasDerivAt (fun r => ∫ u in t₀..r, q u) (q t) t :=
    intervalIntegral.integral_hasDerivAt_right ((hq.mono hsub).intervalIntegrable)
      (hq.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hq.continuousAt (isOpen_Ioo.mem_nhds ht))
  convert hi.neg.exp.mul hf using 1
  simp only [Pi.neg_apply]
  ring

/-- Positive representation gives a strictly increasing actual integrating
 factor, and hence the full decreasing/increasing shape of Gamma'. -/
theorem crossing_shape_of_positive_representation
    (G dG f f' q Z : ℝ → ℝ) (a b t₀ : ℝ) (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) (hq : ContinuousOn q (Ioo a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Ioo a b, 0 < f' t - q t * f t)
    (hG : ∀ t ∈ Ioo a b, HasDerivAt G (dG t) t)
    (hZ : ∀ t ∈ Ioo a b, 0 < Z t)
    (hfactor : ∀ t ∈ Ioo a b, dG t = Z t * f t) :
    ∃ c ∈ Icc a b,
      StrictAntiOn G (Ioc a c ∩ Ioo a b) ∧
      StrictMonoOn G (Ico c b ∩ Ioo a b) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(∫ u in t₀..t, q u)) * f t
  have hd : ∀ t ∈ Ioo a b,
      HasDerivAt g (Real.exp (-(∫ u in t₀..t, q u)) * (f' t - q t * f t)) t := by
    intro t ht
    exact hasDerivAt_crossing_integrating_factor f f' q a b t₀ t ht₀ ht hq (hf t ht)
  have hg : ContinuousOn g (Ioo a b) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn g (Ioo a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo a b) hg
    intro t ht
    rw [interior_Ioo] at ht
    rw [(hd t ht).deriv]
    exact mul_pos (Real.exp_pos _) (hpos t ht)
  apply crossing_shape_of_positive_factor G dG g
    (fun t => Z t / Real.exp (-(∫ u in t₀..t, q u))) a b hab hG hg hmono
  · intro t ht
    exact div_pos (hZ t ht) (Real.exp_pos _)
  · intro t ht
    rw [hfactor t ht]
    dsimp [g]
    field_simp

end FRSB
