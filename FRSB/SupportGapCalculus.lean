module

public import FRSB.CrossingShape
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! The actual calculus contradiction used to exclude support gaps. -/
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB

theorem shaped_function_le_endpoints (g : ℝ → ℝ) {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Icc a b) (hg : ContinuousOn g (Icc a b))
    (hanti : StrictAntiOn g (Ioc a c ∩ Ioo a b))
    (hmono : StrictMonoOn g (Ico c b ∩ Ioo a b)) :
    ∀ x ∈ Icc a b, g x ≤ max (g a) (g b) := by
  intro x hx
  rcases hx.1.eq_or_lt with h | hax
  · subst x
    exact le_max_left _ _
  rcases hx.2.eq_or_lt with h | hxb
  · subst x
    exact le_max_right _ _
  by_cases hxc : x ≤ c
  · have hxI : x ∈ Ioc a c ∩ Ioo a b := ⟨⟨hax, hxc⟩, ⟨hax, hxb⟩⟩
    have hn : (𝓝[Ioo a x] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo hax.ne]
      exact ⟨le_rfl, hax.le⟩)
    have hs : Ioo a x ⊆ Icc a b := by
      intro y hy
      exact ⟨hy.1.le, hy.2.le.trans hx.2⟩
    have ht := (hg a ⟨le_rfl, hab.le⟩).mono hs
    have hle : g x ≤ g a := ge_of_tendsto ht.tendsto (by
      filter_upwards [self_mem_nhdsWithin (s := Ioo a x) (a := a)] with y hy
      exact (hanti ⟨⟨hy.1, hy.2.le.trans hxc⟩, ⟨hy.1, hy.2.trans hxb⟩⟩ hxI hy.2).le)
    exact hle.trans (le_max_left _ _)
  · have hcx : c ≤ x := (lt_of_not_ge hxc).le
    have hxI : x ∈ Ico c b ∩ Ioo a b := ⟨⟨hcx, hxb⟩, ⟨hax, hxb⟩⟩
    have hn : (𝓝[Ioo x b] b).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ioo hxb.ne]
      exact ⟨hxb.le, le_rfl⟩)
    have hs : Ioo x b ⊆ Icc a b := by
      intro y hy
      exact ⟨hx.1.trans hy.1.le, hy.2.le⟩
    have ht := (hg b ⟨hab.le, le_rfl⟩).mono hs
    have hle : g x ≤ g b := ge_of_tendsto ht.tendsto (by
      filter_upwards [self_mem_nhdsWithin (s := Ioo x b) (a := b)] with y hy
      exact (hmono hxI ⟨⟨hcx.trans hy.1.le, hy.2⟩, ⟨hax.trans hy.1, hy.2⟩⟩ hy.1).le)
    exact hle.trans (le_max_right _ _)

theorem no_gap_of_crossing_shape (F g : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt F (g x) x)
    (hFa : F a = a) (hFb : F b = b) (hga : g a ≤ 1) (hgb : g b ≤ 1)
    (hshape : ∃ c ∈ Icc a b,
      StrictAntiOn g (Ioc a c ∩ Ioo a b) ∧ StrictMonoOn g (Ico c b ∩ Ioo a b)) : False := by
  obtain ⟨c, hc, hanti, hmono⟩ := hshape
  have hle : ∀ x ∈ Icc a b, g x ≤ 1 := by
    intro x hx
    exact (shaped_function_le_endpoints g hab hc hg hanti hmono x hx).trans
      (max_le hga hgb)
  have hgi : IntervalIntegrable g volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab.le] using hg
  have hint : (∫ x in a..b, g x) = b - a := by
    simpa only [hFa, hFb] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hF hderiv hgi
  have hi : IntervalIntegrable (fun x => 1 - g x) volume a b :=
    intervalIntegrable_const.sub hgi
  have hzero : (∫ x in a..b, 1 - g x) = 0 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hgi,
      intervalIntegral.integral_const, smul_eq_mul, mul_one, hint]
    ring
  have hae : (fun x => 1 - g x) =ᵐ[volume.restrict (Ioc a b)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact sub_nonneg.mpr (hle x ⟨hx.1.le, hx.2⟩)) hi).mp hzero
  have hconst : ∀ x ∈ Ioc a b, g x = 1 := by
    have heq := Measure.eqOn_Ioc_of_ae_eq (μ := volume) hae
      (continuousOn_const.sub (hg.mono Ioc_subset_Icc_self)) continuousOn_const
    intro x hx
    have h := heq hx
    change 1 - g x = 0 at h
    linarith
  by_cases hac : a < c
  · let x := (2 * a + c) / 3
    let y := (a + 2 * c) / 3
    have hx : x ∈ Ioc a c ∩ Ioo a b := by dsimp [x]; constructor <;> constructor <;> linarith [hc.2]
    have hy : y ∈ Ioc a c ∩ Ioo a b := by dsimp [y]; constructor <;> constructor <;> linarith [hc.2]
    have hxy : x < y := by dsimp [x, y]; linarith
    have h := hanti hx hy hxy
    rw [hconst x ⟨hx.2.1, hx.2.2.le⟩, hconst y ⟨hy.2.1, hy.2.2.le⟩] at h
    exact lt_irrefl _ h
  · have hca : c = a := by linarith [hc.1]
    subst c
    let x := (2 * a + b) / 3
    let y := (a + 2 * b) / 3
    have hx : x ∈ Ico a b ∩ Ioo a b := by dsimp [x]; constructor <;> constructor <;> linarith
    have hy : y ∈ Ico a b ∩ Ioo a b := by dsimp [y]; constructor <;> constructor <;> linarith
    have hxy : x < y := by dsimp [x, y]; linarith
    have h := hmono hx hy hxy
    rw [hconst x ⟨hx.2.1, hx.2.2.le⟩, hconst y ⟨hy.2.1, hy.2.2.le⟩] at h
    exact lt_irrefl _ h

end FRSB
