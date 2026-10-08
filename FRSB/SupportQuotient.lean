module

public import FRSB.MomentQuotient
public import FRSB.QuotientContinuity
public import FRSB.CurvatureIdentity
public import FRSB.Optimality
public import FRSB.SupportGeometry

@[expose] public section

/-! The actual moment quotient on an interval of minimizing support. The
support interval is the geometric conclusion of Section 6.1, rather than
an analytic assumption about the selected PDE or diffusion. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

theorem Gamma_eq_identity_on_support_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∀ s ∈ Icc (0 : ℝ) q, Gamma β μ s = s := by
  intro s hs
  have hmem : s ∈ parisiSupport μ := hsupp ▸ hs
  obtain ⟨u, hu, rfl⟩ := hmem
  exact Gamma_eq_overlap_of_support β hβ μ hmin u hu

theorem GammaPrime_eq_one_on_support_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∀ s ∈ Icc (0 : ℝ) q, GammaPrime β μ s = 1 := by
  intro s hs
  have hu := uniqueDiffOn_Icc hq s hs
  have hd := (hasDerivWithinAt_Gamma_GammaPrime β hβ μ
    ⟨hs.1, hs.2.trans hq1⟩).mono
      (show Icc (0 : ℝ) q ⊆ Icc (0 : ℝ) 1 from fun _ ht => ⟨ht.1,ht.2.trans hq1⟩)
  have hi : HasDerivWithinAt (Gamma β μ) 1 (Icc (0 : ℝ) q) s :=
    (hasDerivWithinAt_id s (Icc (0 : ℝ) q)).congr
      (Gamma_eq_identity_on_support_interval β hβ μ hmin q hsupp)
      (Gamma_eq_identity_on_support_interval β hβ μ hmin q hsupp s hs)
  exact hd.derivWithin hu |>.symm.trans (hi.derivWithin hu)

theorem fixedStateNumerator_eq (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    fixedStateJetPower β hβ μ μ 2 2 s = quotientNumerator β μ s := by
  rw [fixedStateJetPower_self_physical β hβ μ 2 2 hs]
  simp only [quotientNumerator, quotientNumeratorPolynomial, moment_X_pow]

theorem fixedStateDenominator_eq (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    fixedStateJetPower β hβ μ μ 1 3 s = quotientDenominator β μ s := by
  rw [fixedStateJetPower_self_physical β hβ μ 1 3 hs]
  simp only [quotientDenominator, quotientDenominatorPolynomial, moment_X_pow]

/-- Lemma 6.2's literal pointwise formula for the actual CDF, including
zero. The only geometric premise is that the minimizing support is [0,q]. -/
theorem parisiCDF_eq_momentQuotient_on_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ∀ s ∈ Ico (0 : ℝ) q, parisiCDF μ s = momentQuotient β μ s := by
  let A := fixedStateJetPower β hβ μ μ 2 2
  let B := fixedStateJetPower β hβ μ μ 1 3
  have hAB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) q) :
      A s = quotientNumerator β μ s ∧ B s = quotientDenominator β μ s :=
    ⟨fixedStateNumerator_eq β hβ μ ⟨hs.1,hs.2.trans hq1⟩,
      fixedStateDenominator_eq β hβ μ ⟨hs.1,hs.2.trans hq1⟩⟩
  have hG := GammaPrime_eq_one_on_support_interval β hβ μ hmin q hq hq1 hsupp
  have hi : ∀ s t, s ∈ Icc (0 : ℝ) q → t ∈ Icc (0 : ℝ) q → s ≤ t →
      ∫ r in s..t, A r - 2 * parisiCDF μ r * B r = 0 := by
    intro s t hs ht _hst
    have hh := curvatureMoment2_interval_integral β hβ μ
      ⟨hs.1,hs.2.trans hq1⟩ ⟨ht.1,ht.2.trans hq1⟩
    have hzero : curvatureMoment2 β μ t - curvatureMoment2 β μ s = 0 := by
      have hg1 := hG s hs
      have hg2 := hG t ht
      unfold GammaPrime at hg1 hg2
      exact (mul_eq_zero.mp (show β ^ 2 * (curvatureMoment2 β μ t -
        curvatureMoment2 β μ s) = 0 by nlinarith)).resolve_left (pow_ne_zero 2 hβ)
    rw [hzero] at hh
    have he : (∫ r in s..t, curvatureEvolutionSource β hβ μ μ r) =
        β ^ 2 * ∫ r in s..t, A r - 2 * parisiCDF μ r * B r := by
      rw [← intervalIntegral.integral_const_mul]
      rfl
    rw [he] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero 2 hβ)
  have hBpos : ∀ s ∈ Icc (0 : ℝ) q, 0 < B s := by
    intro s hs
    rw [(hAB s hs).2]
    exact quotientDenominator_pos β hβ μ s ⟨hs.1,hs.2.trans hq1⟩
  have he := quotient_of_interval_identity (parisiCDF μ) A B q
    (continuous_fixedStateJetPower β hβ μ μ 2 2).stronglyMeasurable
    (continuous_fixedStateJetPower β hβ μ μ 1 3).stronglyMeasurable
    (parisiCDF_measurable μ).stronglyMeasurable
    (continuous_fixedStateJetPower β hβ μ μ 2 2).continuousOn
    (continuous_fixedStateJetPower β hβ μ μ 1 3).continuousOn
    hBpos
    (fun s _ => parisiCDF_continuousWithinAt_right μ s) hi
  intro s hs
  rw [he s hs, (hAB s ⟨hs.1,hs.2.le⟩).1, (hAB s ⟨hs.1,hs.2.le⟩).2]
  rfl

/-- The quotient formula rules out an atom at the origin. -/
theorem parisiMeasure_no_atom_zero_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    (μ : Measure Overlap) {⟨0, by simp⟩} = 0 :=
  parisiMeasure_no_atom_zero_of_quotient μ (quotientNumerator β μ)
    (quotientDenominator β μ) q hq (quotientNumerator_initial_zero β μ)
    (parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq hq1 hsupp)

/-- The smooth extension's endpoint value is the actual mass below q. -/
theorem momentQuotient_terminal_mass_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ((μ : Measure Overlap) {x | (x : ℝ) < q}).toReal = momentQuotient β μ q :=
  parisiCDF_quotient_terminal_mass μ (quotientNumerator β μ)
    (quotientDenominator β μ) q hq
    ((continuousOn_quotientNumerator β hβ μ).mono (fun _ hs => ⟨hs.1,hs.2.trans hq1⟩))
    ((continuousOn_quotientDenominator β hβ μ).mono (fun _ hs => ⟨hs.1,hs.2.trans hq1⟩))
    (fun s hs => quotientDenominator_pos β hβ μ s ⟨hs.1,hs.2.trans hq1⟩)
    (parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq hq1 hsupp)

end FRSB
