module

public import FRSB.PolynomialMomentGrid
public import FRSB.ParisiGridTopology

@[expose] public section

/-! The actual all-polynomial moment evolution for every overlap law. The
identity comes from genuine finite-cell Itô calculus and weak approximation;
no stochastic or evolution identity is supplied as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FRSB

theorem tendsto_fixedStatePolynomialMoment_of_weak {ι : Type*} {L : Filter ι}
    (β : ℝ) (hβ : β ≠ 0) (μ ρ : ParisiMeasure) (ν : ι → ParisiMeasure)
    (hν : Tendsto ν L (nhds ρ)) (f : MomentPolynomial) (t : ℝ) :
    Tendsto (fun i => fixedStatePolynomialMoment β hβ μ (ν i) f t) L
      (nhds (fixedStatePolynomialMoment β hβ μ ρ f t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => fixedStatePolynomialMoment_sub_norm_le β hβ μ (ν i) ρ f t)
  have hh := ((continuous_polynomialJetBCF β f).tendsto ρ).comp hν
    |>.sub_const (polynomialJetBCF β ρ f) |>.norm
  simpa only [Function.comp_apply,sub_self,norm_zero] using hh

theorem moment_tail_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    moment β μ f 1-moment β μ f s =
      ∫t in s..1,polynomialMomentSource β hβ μ μ f t := by
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => gridPolynomialMoment β hβ μ f n t) atTop
        (nhds (moment β μ f t)) := by
    have hh := tendsto_fixedStatePolynomialMoment_of_weak β hβ μ μ
      (parisiGridMeasure μ) (tendsto_parisiGridMeasure μ) f t
    rw [fixedStatePolynomialMoment_self_physical β hβ μ f ht] at hh
    exact hh
  have hS := tendsto_polynomialMomentSource_integral_of_weak β hβ μ μ
    (parisiGridMeasure μ) (tendsto_parisiGridMeasure μ) f s 1
  have hleft := ((hF 1 ⟨by norm_num,le_rfl⟩).sub (hF s hs)).sub hS |>.norm
  have hright : Tendsto (fun n => β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*
      parisiCDFDistance μ (parisiGridMeasure μ n)+
        uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*
          parisiHJBGradientError β μ n)) atTop (nhds 0) := by
    simpa only [mul_zero,zero_add] using
      (((tendsto_parisiCDFDistance_grid μ).const_mul
        (uniformPolynomialMomentBound β (momentDrift1 f)+
          uniformPolynomialMomentBound β (polynomialSpatialDerivative f))).add
      ((tendsto_parisiHJBGradientError β hβ μ).const_mul
        (uniformPolynomialMomentBound β (polynomialSpatialDerivative f)))).const_mul (β^2)
  have hh := le_of_tendsto_of_tendsto hleft hright
    (.of_forall fun n => gridPolynomial_tail_remainder_le β hβ μ f n hs)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

/-- Endpoint order is unrestricted, so this is the full interval identity. -/
theorem moment_interval_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    moment β μ f t-moment β μ f r =
      ∫s in r..t,polynomialMomentSource β hβ μ μ f s := by
  have hR := moment_tail_integral β hβ μ f hr
  have hT := moment_tail_integral β hβ μ f ht
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (polynomialMomentSource_intervalIntegrable β hβ μ μ f r t)
    (polynomialMomentSource_intervalIntegrable β hβ μ μ f t 1)
  linarith

theorem moment_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    moment β μ f t = moment β μ f 0+
      ∫s in 0..t,polynomialMomentSource β hβ μ μ f s := by
  have hh := moment_interval_integral β hβ μ f ⟨le_rfl,by norm_num⟩ ht
  linarith

theorem polynomialMomentSource_self_physical (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (f : MomentPolynomial) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    polynomialMomentSource β hβ μ μ f t =
      β^2*(moment β μ (momentDrift0 f) t+parisiCDF μ t*moment β μ (momentDrift1 f) t) := by
  unfold polynomialMomentSource
  rw [fixedStatePolynomialMoment_self_physical β hβ μ (momentDrift0 f) ht,
    fixedStatePolynomialMoment_self_physical β hβ μ (momentDrift1 f) ht]

/-- Literal universal Itô polynomial law, with both drift polynomials evaluated
on the actual state and actual spatial jets. -/
theorem moment_interval_integral_physical (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    moment β μ f t-moment β μ f r = β^2*∫s in r..t,
      moment β μ (momentDrift0 f) s+parisiCDF μ s*moment β μ (momentDrift1 f) s := by
  rw [moment_interval_integral β hβ μ f hr ht,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro s hs
  exact polynomialMomentSource_self_physical β hβ μ f
    (uIcc_subset_Icc hr ht ⟨hs.1.le,hs.2.le⟩)

end FRSB
