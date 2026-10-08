module

public import FRSB.CrossingCovariance

@[expose] public section

/-! The normalized positive half-line density used in Section 5, with its
 genuine probability normalization and the nondegeneracy needed for strict
 covariance. -/
noncomputable section
open Set Filter MeasureTheory Measure ProbabilityTheory
namespace FRSB

def crossingWeightMass (ω : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), ω x

def crossingWeightLaw (ω : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun x => ENNReal.ofReal (ω x / crossingWeightMass ω))

theorem crossingWeightMass_pos (ω : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x) :
    0 < crossingWeightMass ω := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] ω := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hp x hx).le
  apply (integral_pos_iff_support_of_nonneg_ae hn hω).mpr
  have hs : Ioo (0 : ℝ) 1 ⊆ Function.support ω := by
    intro x hx
    exact (hp x hx.1).ne'
  have hv : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo (0 : ℝ) 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr Ioo_subset_Ioi_self]
    simp
  exact hv.trans_le (measure_mono hs)

theorem crossingWeightLaw_isProbability (ω : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x) :
    IsProbabilityMeasure (crossingWeightLaw ω) := by
  have hZ := crossingWeightMass_pos ω hω hp
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => ω x / crossingWeightMass ω) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (div_pos (hp x hx) hZ).le
  constructor
  rw [crossingWeightLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hω.div_const _) hn, integral_div]
  change ENNReal.ofReal (crossingWeightMass ω / crossingWeightMass ω) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]

theorem crossingWeightLaw_halfLine (ω : ℝ → ℝ) :
    ∀ᵐ x ∂crossingWeightLaw ω, x ∈ Ici (0 : ℝ) := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (show 0 < x from hx).le

theorem crossingWeightLaw_base_absolutelyContinuous (ω : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x) :
    volume.restrict (Ioi (0 : ℝ)) ≪ crossingWeightLaw ω := by
  apply withDensity_absolutelyContinuous' (hω.aestronglyMeasurable.aemeasurable.div_const
    (crossingWeightMass ω)).ennreal_ofReal
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (ENNReal.ofReal_pos.mpr (div_pos (hp x hx) (crossingWeightMass_pos ω hω hp))).ne'

/-- The two concrete separated sets used to certify strict covariance. -/
theorem crossingWeightLaw_ordered_masses_pos (ω : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x) :
    0 < crossingWeightLaw ω (Icc (0 : ℝ) 1) ∧ 0 < crossingWeightLaw ω (Ici 2) := by
  have hac := crossingWeightLaw_base_absolutelyContinuous ω hω hp
  have hv1 : 0 < (volume.restrict (Ioi (0 : ℝ))) (Icc (0 : ℝ) 1) := by
    rw [Measure.restrict_apply measurableSet_Icc]
    have hs : Icc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨⟨_, hx1⟩, hx0⟩; exact ⟨hx0, hx1⟩
      · rintro ⟨hx0, hx1⟩; exact ⟨⟨hx0.le, hx1⟩, hx0⟩
    rw [hs]
    simp
  have hv2 : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ici (2 : ℝ)) := by
    rw [Measure.restrict_apply measurableSet_Ici,
      inter_eq_left.mpr (show Ici (2 : ℝ) ⊆ Ioi 0 from fun x hx => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx)]
    simp
  exact ⟨pos_iff_ne_zero.mpr (fun h => hv1.ne' (hac h)),
    pos_iff_ne_zero.mpr (fun h => hv2.ne' (hac h))⟩

theorem crossingCovariance_pos_of_positive_weight (ω f g : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x)
    (hfi : Integrable f (crossingWeightLaw ω)) (hgi : Integrable g (crossingWeightLaw ω))
    (hfgi : Integrable (fun x => f x * g x) (crossingWeightLaw ω))
    (hf : StrictMonoOn f (Ici 0)) (hg : StrictMonoOn g (Ici 0)) :
    0 < crossingCovariance (crossingWeightLaw ω) f g := by
  have := crossingWeightLaw_isProbability ω hω hp
  obtain ⟨hm1, hm2⟩ := crossingWeightLaw_ordered_masses_pos ω hω hp
  exact crossingCovariance_pos _ f g hfi hgi hfgi (crossingWeightLaw_halfLine ω)
    hf hg 1 2 (by norm_num) (by norm_num) hm1 hm2

/-- Expectations against the genuine normalized density are exactly the
 weighted half-line integrals divided by their positive mass. -/
theorem integral_crossingWeightLaw (ω f : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x) :
    (∫ x, f x ∂crossingWeightLaw ω) =
      (∫ x in Ioi (0 : ℝ), f x * ω x) / crossingWeightMass ω := by
  have hm := (hω.aestronglyMeasurable.aemeasurable.div_const (crossingWeightMass ω)).ennreal_ofReal
  rw [crossingWeightLaw, integral_withDensity_eq_integral_toReal_smul₀ hm
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x in Ioi (0 : ℝ), (f x * ω x) / crossingWeightMass ω := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [ENNReal.toReal_ofReal (div_pos (hp x hx) (crossingWeightMass_pos ω hω hp)).le,
        smul_eq_mul]
      ring
    _ = _ := integral_div _ _

theorem integrable_crossingWeightLaw_of_weighted (ω f : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x)
    (hf : IntegrableOn (fun x => f x * ω x) (Ioi (0 : ℝ))) :
    Integrable f (crossingWeightLaw ω) := by
  have hm := (hω.aestronglyMeasurable.aemeasurable.div_const (crossingWeightMass ω)).ennreal_ofReal
  apply (integrable_withDensity_iff_integrable_smul₀' hm
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).mpr
  apply (hf.div_const (crossingWeightMass ω)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (div_pos (hp x hx) (crossingWeightMass_pos ω hω hp)).le,
    smul_eq_mul]
  ring

end FRSB
