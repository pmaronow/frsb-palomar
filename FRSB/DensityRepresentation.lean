module

public import FRSB.QuotientContinuity

@[expose] public section

/-! Identification of a genuine probability measure from a smooth CDF on
 [0,q), retaining the terminal atom and the one-sided endpoint derivative. -/
noncomputable section
open Set Filter MeasureTheory Measure ProbabilityTheory
open scoped Topology ContDiff
namespace FRSB

def smoothCDFDensity (F : ℝ → ℝ) (q : ℝ) : ℝ → ℝ := derivWithin F (Icc 0 q)

def smoothCDFDensityMeasure (F : ℝ → ℝ) (q : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) q)).withDensity (fun x => ENNReal.ofReal (smoothCDFDensity F q x))

theorem smoothCDFDensityMeasure_eq_Ico (F : ℝ → ℝ) (q : ℝ) :
    smoothCDFDensityMeasure F q = (volume.restrict (Ico (0 : ℝ) q)).withDensity
      (fun x => ENNReal.ofReal (smoothCDFDensity F q x)) := by
  unfold smoothCDFDensityMeasure
  rw [restrict_Ico_eq_restrict_Icc]

theorem tendsto_cdf_left_mass (ν : Measure ℝ) [IsProbabilityMeasure ν] (q : ℝ) :
    Tendsto (cdf ν) (𝓝[<] q) (𝓝 ((ν (Iio q)).toReal)) := by
  have hl := (cdf ν).mono.tendsto_leftLim q
  have hn : 0 ≤ Function.leftLim (cdf ν) q :=
    ge_of_tendsto hl (Filter.Eventually.of_forall (cdf_nonneg ν))
  have hm : (ν (Iio q)).toReal = Function.leftLim (cdf ν) q := by
    calc
      _ = (((cdf ν).measure) (Iio q)).toReal := by rw [measure_cdf]
      _ = _ := by
        rw [StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot ν), sub_zero,
          ENNReal.toReal_ofReal hn]
  exact hm ▸ hl

theorem cdf_continuous_extension_terminal_mass (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q) (hc : ContinuousOn F (Icc 0 q))
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = (ν (Iic s)).toReal) :
    (ν (Iio q)).toReal = F q := by
  have hlim : Tendsto F (𝓝[<] q) (𝓝 (F q)) := by
    have hh := (hc q ⟨hq.le, le_rfl⟩).mono Ioo_subset_Icc_self
    simpa only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hq] using hh
  have hevent : (cdf ν : ℝ → ℝ) =ᶠ[𝓝[<] q] F := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hq]
    apply eventually_nhdsWithin_of_forall
    intro s hs
    rw [cdf_eq_real, measureReal_def, ← he s ⟨hs.1.le, hs.2⟩]
  exact tendsto_nhds_unique (tendsto_cdf_left_mass ν q) (hlim.congr' hevent.symm)

theorem monotoneOn_continuous_cdf_extension (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q) (hc : ContinuousOn F (Icc 0 q))
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = (ν (Iic s)).toReal) :
    MonotoneOn F (Icc 0 q) := by
  have hFq := cdf_continuous_extension_terminal_mass ν F q hq hc he
  intro x hx y hy hxy
  by_cases hyq : y < q
  · rw [he x ⟨hx.1, hxy.trans_lt hyq⟩, he y ⟨hy.1, hyq⟩]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hxy))
  have hy' : y = q := le_antisymm hy.2 (le_of_not_gt hyq)
  subst y
  by_cases hxq : x = q
  · subst x; exact le_rfl
  have hxlt : x < q := lt_of_le_of_ne hx.2 hxq
  rw [he x ⟨hx.1, hxlt⟩, ← hFq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun z hz => hz.trans_lt hxlt))

/-- A smooth CDF extension has an actual smooth nonnegative density,
 including its two one-sided endpoint values. -/
theorem smoothCDFDensity_regular (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q) (hc : ContDiffOn ℝ ∞ F (Icc 0 q))
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = (ν (Iic s)).toReal) :
    ContDiffOn ℝ ∞ (smoothCDFDensity F q) (Icc 0 q) ∧
      ∀ s ∈ Icc (0 : ℝ) q, 0 ≤ smoothCDFDensity F q s := by
  have hm := monotoneOn_continuous_cdf_extension ν F q hq hc.continuousOn he
  refine ⟨hc.derivWithin (uniqueDiffOn_Icc hq) (by simp), ?_⟩
  intro s hs
  exact hm.derivWithin_nonneg

/-- The density measure's cumulative mass is the primitive difference. -/
theorem smoothCDFDensityMeasure_Iic (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (hF0 : F 0 = 0)
    (hm : MonotoneOn F (Icc 0 q)) (s : ℝ) :
    smoothCDFDensityMeasure F q (Iic s) =
      if s < 0 then 0 else if s < q then ENNReal.ofReal (F s) else ENNReal.ofReal (F q) := by
  have hr : ContinuousOn (smoothCDFDensity F q) (Icc 0 q) :=
    (hc.derivWithin (m := ∞) (uniqueDiffOn_Icc hq) (by simp)).continuousOn
  have hn : ∀ x, 0 ≤ smoothCDFDensity F q x := fun x => hm.derivWithin_nonneg
  have hd : ∀ x ∈ Icc (0 : ℝ) q,
      HasDerivWithinAt F (smoothCDFDensity F q x) (Icc 0 q) x := by
    intro x hx
    exact (hc.differentiableOn (by simp) x hx).hasDerivWithinAt
  have hFTC : ∀ t ∈ Icc (0 : ℝ) q, ∫ x in 0..t, smoothCDFDensity F q x = F t := by
    intro t ht
    have hi : ∫ x in 0..t, smoothCDFDensity F q x = F t - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
        (hc.continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
      · intro x hx
        exact ((hd x ⟨hx.1.le, hx.2.le.trans ht.2⟩).hasDerivAt
          (Icc_mem_nhds hx.1 (hx.2.trans_le ht.2))).hasDerivWithinAt
      · exact (hr.mono (uIcc_subset_Icc ⟨le_rfl, hq.le⟩ ht)).intervalIntegrable
    simpa only [hF0, sub_zero] using hi
  have hmeasure (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
      (∫⁻ x in Icc (0 : ℝ) t, ENNReal.ofReal (smoothCDFDensity F q x)) = ENNReal.ofReal (F t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hr.mono (Icc_subset_Icc le_rfl ht.2)).integrableOn_Icc)
      (Filter.Eventually.of_forall hn), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.1, hFTC t ht]
  unfold smoothCDFDensityMeasure
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  by_cases hs0 : s < 0
  · rw [ite_eq_left hs0]
    have hi : Iic s ∩ Icc (0 : ℝ) q = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      rintro ⟨hx, hx0, _⟩
      linarith
    rw [hi]
    simp
  rw [ite_eq_right hs0]
  by_cases hsq : s < q
  · rw [ite_eq_left hsq]
    have hi : Iic s ∩ Icc (0 : ℝ) q = Icc 0 s := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxs, hx0, _⟩; exact ⟨hx0, hxs⟩
      · rintro ⟨hx0, hxs⟩; exact ⟨hxs, hx0, hxs.trans hsq.le⟩
    rw [hi]
    exact hmeasure s ⟨le_of_not_gt hs0, hsq.le⟩
  · rw [ite_eq_right hsq]
    rw [inter_eq_right.mpr (fun x hx => hx.2.trans (le_of_not_gt hsq))]
    exact hmeasure q ⟨hq.le, le_rfl⟩

/-- Exact density-plus-terminal-atom identification for a probability law
 carried by [0,q]. No first variation or PDE premise is hidden in the proof. -/
theorem probabilityMeasure_eq_smooth_density_add_terminal_atom
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hs : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (hF0 : F 0 = 0)
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = (ν (Iic s)).toReal) :
    ν = smoothCDFDensityMeasure F q + ENNReal.ofReal (1 - F q) • Measure.dirac q := by
  have hm := monotoneOn_continuous_cdf_extension ν F q hq hc.continuousOn he
  have hFq := cdf_continuous_extension_terminal_mass ν F q hq hc.continuousOn he
  have hnq : 0 ≤ F q := by rw [← hFq]; exact ENNReal.toReal_nonneg
  have hlq : F q ≤ 1 := by
    rw [← hFq]
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (measure_mono (subset_univ (Iio q)) |>.trans_eq (measure_univ : ν univ = 1))
  apply Measure.ext_of_Iic
  intro s
  rw [Measure.add_apply,
    smoothCDFDensityMeasure_Iic F q hq hc hF0 hm, Measure.smul_apply,
    Measure.dirac_apply' q measurableSet_Iic]
  by_cases hs0 : s < 0
  · rw [ite_eq_left hs0, indicator_of_notMem (show q ∉ Iic s by exact not_le.mpr (hs0.trans hq)),
      smul_zero, add_zero]
    have hsnull : ν {x : ℝ | x ∉ Icc (0 : ℝ) q} = 0 := ae_iff.mp hs
    exact measure_mono_null (fun x hx => by intro hx'; exact not_le_of_gt (hx.trans_lt hs0) hx'.1) hsnull
  rw [ite_eq_right hs0]
  by_cases hsq : s < q
  · rw [ite_eq_left hsq, indicator_of_notMem (show q ∉ Iic s from not_le.mpr hsq), smul_zero, add_zero,
      he s ⟨le_of_not_gt hs0, hsq⟩, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [ite_eq_right hsq, indicator_of_mem (show q ∈ Iic s from le_of_not_gt hsq), smul_eq_mul, Pi.one_apply, mul_one,
      ← ENNReal.ofReal_add hnq (sub_nonneg.mpr hlq)]
    have hh : F q + (1 - F q) = 1 := by ring
    rw [hh, ENNReal.ofReal_one]
    have hevent : Iic s =ᵐ[ν] univ := by
      filter_upwards [hs] with x hx
      simp only [mem_Iic, mem_univ]
      exact propext (iff_true_intro (hx.2.trans (le_of_not_gt hsq)))
    rw [measure_congr hevent, measure_univ]

/-- The terminal atom has exactly the missing mass of the smooth left CDF. -/
theorem probabilityMeasure_terminal_atom_of_smooth_cdf
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hs : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (hF0 : F 0 = 0)
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = (ν (Iic s)).toReal) :
    ν {q} = ENNReal.ofReal (1 - F q) := by
  have hρ : smoothCDFDensityMeasure F q {q} = 0 := by
    unfold smoothCDFDensityMeasure
    exact measure_singleton q
  rw [probabilityMeasure_eq_smooth_density_add_terminal_atom ν F q hq hs hc hF0 he,
    Measure.add_apply, hρ, zero_add, Measure.smul_apply]
  simp

/-- The density is the genuine within derivative, at both endpoints as well
 as in the interior. In particular no two-sided differentiability is asserted
 across the terminal atom. -/
theorem smoothCDFDensity_hasDerivWithinAt (F : ℝ → ℝ) (q : ℝ)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) q) :
    HasDerivWithinAt F (smoothCDFDensity F q s) (Icc 0 q) s :=
  (hc.differentiableOn (by simp) s hs).hasDerivWithinAt

theorem smoothCDFDensity_hasDerivAt_endpoints (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) :
    HasDerivWithinAt F (smoothCDFDensity F q 0) (Ici 0) 0 ∧
      HasDerivWithinAt F (smoothCDFDensity F q q) (Iic q) q := by
  constructor
  · have hd := smoothCDFDensity_hasDerivWithinAt F q hc 0 ⟨le_rfl, hq.le⟩
    simpa only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsGE hq] using hd
  · have hd := smoothCDFDensity_hasDerivWithinAt F q hc q ⟨hq.le, le_rfl⟩
    simpa only [HasDerivWithinAt, nhdsWithin_Icc_eq_nhdsLE hq] using hd

/-- Specialization to the actual overlap law embedded in the real line. -/
theorem parisiMeasure_eq_smooth_density_add_terminal_atom
    (μ : Paper.ParisiMeasure) (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hs : ∀ᵐ (x : Paper.Overlap) ∂(μ : Measure Paper.Overlap),
      (x : ℝ) ∈ Icc (0 : ℝ) q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (hF0 : F 0 = 0)
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = Paper.parisiCDF μ s) :
    (μ : Measure Paper.Overlap).map (fun x : Paper.Overlap => (x : ℝ)) =
      smoothCDFDensityMeasure F q + ENNReal.ofReal (1 - F q) • Measure.dirac q := by
  apply probabilityMeasure_eq_smooth_density_add_terminal_atom _ F q hq
  · exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_Icc)).mpr hs
  · exact hc
  · exact hF0
  · intro s hs
    rw [he s hs, Measure.map_apply measurable_subtype_coe measurableSet_Iic]
    rfl

/-- Exact endpoint mass in the original overlap space, with no choice of
 a real-line representative of the overlap needed. -/
theorem parisiMeasure_terminal_atom_of_smooth_cdf
    (μ : Paper.ParisiMeasure) (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hs : ∀ᵐ (x : Paper.Overlap) ∂(μ : Measure Paper.Overlap),
      (x : ℝ) ∈ Icc (0 : ℝ) q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (hF0 : F 0 = 0)
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = Paper.parisiCDF μ s) :
    (μ : Measure Paper.Overlap) {x | (x : ℝ) = q} = ENNReal.ofReal (1 - F q) := by
  have hr := parisiMeasure_eq_smooth_density_add_terminal_atom μ F q hq hs hc hF0 he
  have hρ : smoothCDFDensityMeasure F q {q} = 0 := by
    unfold smoothCDFDensityMeasure
    exact measure_singleton q
  have hmass := congrArg (fun ν : Measure ℝ => ν {q}) hr
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton q),
    Measure.add_apply, hρ, zero_add, Measure.smul_apply] at hmass
  have hset : (Subtype.val : Paper.Overlap → ℝ) ⁻¹' {q} =
      {x : Paper.Overlap | (x : ℝ) = q} := by ext x; simp
  rw [hset] at hmass
  simpa using hmass

/-- Literal half-open density convention in the main theorem. -/
theorem parisiMeasure_eq_smooth_density_Ico_add_terminal_atom
    (μ : Paper.ParisiMeasure) (F : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (hs : ∀ᵐ (x : Paper.Overlap) ∂(μ : Measure Paper.Overlap),
      (x : ℝ) ∈ Icc (0 : ℝ) q)
    (hc : ContDiffOn ℝ ∞ F (Icc 0 q)) (hF0 : F 0 = 0)
    (he : ∀ s ∈ Ico (0 : ℝ) q, F s = Paper.parisiCDF μ s) :
    (μ : Measure Paper.Overlap).map (fun x : Paper.Overlap => (x : ℝ)) =
      (volume.restrict (Ico (0 : ℝ) q)).withDensity
        (fun x => ENNReal.ofReal (smoothCDFDensity F q x)) +
      ENNReal.ofReal (1 - F q) • Measure.dirac q := by
  rw [← smoothCDFDensityMeasure_eq_Ico]
  exact parisiMeasure_eq_smooth_density_add_terminal_atom μ F q hq hs hc hF0 he

end FRSB
