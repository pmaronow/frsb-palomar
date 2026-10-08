module

public import FRSB.SupportMomentSmooth

@[expose] public section

/-! The exact density formula and its origin specialization, derived from
actual all-polynomial moment evolution and the positive selected curvature. -/
noncomputable section
open Set Filter MeasureTheory Paper MvPolynomial
open scoped Topology ContDiff
namespace FRSB

def quotientFourthSquarePolynomial : MomentPolynomial := X 3 ^ 2
def quotientMixedPolynomial : MomentPolynomial := X 1 * X 2 ^ 2
def quotientFourthPowerPolynomial : MomentPolynomial := X 1 ^ 4

@[simp] theorem moment_quotientMixedPolynomial (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ quotientMixedPolynomial s =
      ∫ sample, C β μ s sample * D β μ s sample ^ 2 ∂canonicalBrownianMeasure := by
  simp only [quotientMixedPolynomial,moment,momentPolynomialValue,map_mul,map_pow,eval_X]

theorem driftNumerator_zero (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift0 quotientNumeratorPolynomial) s =
      moment β μ quotientFourthSquarePolynomial s := by
  rw [momentDrift0_quotientNumerator_value]
  exact (moment_X_pow β μ 3 2 s).symm

theorem driftNumerator_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift1 quotientNumeratorPolynomial) s =
      -6 * moment β μ quotientMixedPolynomial s := by
  rw [momentDrift1_quotientNumerator_value,moment_quotientMixedPolynomial,
    ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample => by ring

theorem driftDenominator_zero (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift0 quotientDenominatorPolynomial) s =
      3 * moment β μ quotientMixedPolynomial s := by
  rw [momentDrift0_quotientDenominator_value,moment_quotientMixedPolynomial,
    ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun sample => by ring

theorem driftDenominator_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift1 quotientDenominatorPolynomial) s =
      -3 * moment β μ quotientFourthPowerPolynomial s := by
  rw [momentDrift1_quotientDenominator_value]
  change (∫ sample, -3 * C β μ s sample ^ 4 ∂canonicalBrownianMeasure) = _
  rw [integral_const_mul]
  congr 1
  exact (moment_X_pow β μ 1 4 s).symm

/-- The density quotient rule holds at every point of the closed support,
with the terminal coefficient interpreted as the smooth left CDF. -/
theorem parisiSmoothDensity_eq_moment_formula_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    parisiSmoothDensity β μ q t = β ^ 2 *
      (moment β μ quotientFourthSquarePolynomial t -
        12 * momentQuotient β μ t * moment β μ quotientMixedPolynomial t +
        6 * momentQuotient β μ t ^ 2 * moment β μ quotientFourthPowerPolynomial t) /
          (2 * quotientDenominator β μ t) := by
  have hA := hasDerivWithinAt_moment_on_support_interval β hβ μ hmin q hq hq1 hsupp
    quotientNumeratorPolynomial t ht
  have hB := hasDerivWithinAt_moment_on_support_interval β hβ μ hmin q hq hq1 hsupp
    quotientDenominatorPolynomial t ht
  rw [driftNumerator_zero,driftNumerator_one] at hA
  rw [driftDenominator_zero,driftDenominator_one] at hB
  have hBD : quotientDenominator β μ t ≠ 0 :=
    (quotientDenominator_pos β hβ μ t ⟨ht.1,ht.2.trans hq1⟩).ne'
  have hquot : quotientNumerator β μ t =
      2 * momentQuotient β μ t * quotientDenominator β μ t := by
    unfold momentQuotient
    field_simp
  have hd := moment_quotient_density_hasDerivWithinAt
    (quotientNumerator β μ) (quotientDenominator β μ) β (momentQuotient β μ t)
    (moment β μ quotientFourthSquarePolynomial t) (moment β μ quotientMixedPolynomial t)
    (moment β μ quotientFourthPowerPolynomial t) t (Icc 0 q) hBD hquot
    (by convert hA using 1 <;> first | rfl | ring)
    (by convert hB using 1 <;> first | rfl | ring)
  exact hd.derivWithin (uniqueDiffOn_Icc hq t ht)

/-- Literal expectation formula, valid also at q with the left CDF
coefficient given by the continuous quotient extension. -/
theorem parisiSmoothDensity_eq_expectation_formula_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    parisiSmoothDensity β μ q t = β ^ 2 *
      (∫ sample, parisiSpatialJet β μ 4 t (optimalStateReal β μ sample t) ^ 2 -
        12 * momentQuotient β μ t * C β μ t sample * D β μ t sample ^ 2 +
        6 * momentQuotient β μ t ^ 2 * C β μ t sample ^ 4 ∂canonicalBrownianMeasure) /
      (2 * ∫ sample, C β μ t sample ^ 3 ∂canonicalBrownianMeasure) := by
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.trans hq1⟩
  have hAA := integrable_jetProcess_pow β hβ μ 3 2 ht1
  have hCDD : Integrable (fun sample => C β μ t sample * D β μ t sample ^ 2)
      canonicalBrownianMeasure := by
    have he : momentPolynomialValue β μ quotientMixedPolynomial t =
        (fun sample => C β μ t sample * D β μ t sample ^ 2) := by
      funext sample
      simp only [momentPolynomialValue,quotientMixedPolynomial,map_mul,map_pow,eval_X]
    rw [← he]
    exact integrable_momentPolynomialValue β hβ μ quotientMixedPolynomial ht1
  have hC4 := integrable_jetProcess_pow β hβ μ 1 4 ht1
  have he : (fun sample => parisiSpatialJet β μ 4 t (optimalStateReal β μ sample t) ^ 2 -
      12 * momentQuotient β μ t * C β μ t sample * D β μ t sample ^ 2 +
      6 * momentQuotient β μ t ^ 2 * C β μ t sample ^ 4) =
      ((fun sample => jetProcess β μ (3+1) t sample ^ 2) -
        (fun sample => 12 * momentQuotient β μ t * (C β μ t sample * D β μ t sample ^ 2))) +
        (fun sample => 6 * momentQuotient β μ t ^ 2 * jetProcess β μ (1+1) t sample ^ 4) := by
    funext sample
    dsimp only [Pi.add_apply,Pi.sub_apply,C,D,jetProcess]
    ring
  rw [he]
  change parisiSmoothDensity β μ q t = β ^ 2 *
    (∫ sample, (jetProcess β μ (3+1) t sample ^ 2 -
      12 * momentQuotient β μ t * (C β μ t sample * D β μ t sample ^ 2)) +
      6 * momentQuotient β μ t ^ 2 * jetProcess β μ (1+1) t sample ^ 4
      ∂canonicalBrownianMeasure) /
    (2 * ∫ sample, C β μ t sample ^ 3 ∂canonicalBrownianMeasure)
  have hiAdd := integral_add (hAA.sub (hCDD.const_mul (12 * momentQuotient β μ t)))
    (hC4.const_mul (6 * momentQuotient β μ t ^ 2))
  change (∫ sample, (jetProcess β μ (3+1) t sample ^ 2 -
      12 * momentQuotient β μ t * (C β μ t sample * D β μ t sample ^ 2)) +
      6 * momentQuotient β μ t ^ 2 * jetProcess β μ (1+1) t sample ^ 4
      ∂canonicalBrownianMeasure) =
    (∫ sample, jetProcess β μ (3+1) t sample ^ 2 -
      12 * momentQuotient β μ t * (C β μ t sample * D β μ t sample ^ 2)
      ∂canonicalBrownianMeasure) +
    (∫ sample, 6 * momentQuotient β μ t ^ 2 * jetProcess β μ (1+1) t sample ^ 4
      ∂canonicalBrownianMeasure) at hiAdd
  have hiSub := integral_sub hAA (hCDD.const_mul (12 * momentQuotient β μ t))
  change (∫ sample, jetProcess β μ (3+1) t sample ^ 2 -
      12 * momentQuotient β μ t * (C β μ t sample * D β μ t sample ^ 2)
      ∂canonicalBrownianMeasure) =
    (∫ sample, jetProcess β μ (3+1) t sample ^ 2 ∂canonicalBrownianMeasure) -
    (∫ sample, 12 * momentQuotient β μ t * (C β μ t sample * D β μ t sample ^ 2)
      ∂canonicalBrownianMeasure) at hiSub
  rw [hiAdd,hiSub,integral_const_mul,integral_const_mul]
  simpa only [quotientFourthSquarePolynomial,quotientFourthPowerPolynomial,
    quotientDenominator,quotientDenominatorPolynomial,moment_X_pow,
    moment_quotientMixedPolynomial,Nat.reduceAdd]
    using parisiSmoothDensity_eq_moment_formula_of_support_interval
      β hβ μ hmin q hq hq1 hsupp t ht

/-- Genuine one-sided derivatives of the smooth left CDF at both physical
endpoints, including the exact density values defined above. -/
theorem momentQuotient_hasDerivAt_endpoints_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    HasDerivWithinAt (momentQuotient β μ) (parisiSmoothDensity β μ q 0) (Ici 0) 0 ∧
      HasDerivWithinAt (momentQuotient β μ) (parisiSmoothDensity β μ q q) (Iic q) q :=
  smoothCDFDensity_hasDerivAt_endpoints (momentQuotient β μ) q hq
    (moments_contDiffOn_on_support_interval β hβ μ hmin q hq hq1 hsupp).2

@[simp] theorem curvatureMoment2_initial (β : ℝ) (μ : ParisiMeasure) :
    curvatureMoment2 β μ 0 = parisiHessian β μ (0,0) ^ 2 := by
  simp only [curvatureMoment2,C_eq_hessian,optimalState_initial]
  simp

/-- Positive initial curvature chooses the positive self-consistency root. -/
theorem parisiHessian_initial_of_support_interval
    (β : ℝ) (hβ : 0 < β) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    parisiHessian β μ (0,0) = 1 / β := by
  apply curvature_at_zero_of_self_consistency β _ hβ
    (parisiHessian_pos_all β μ 0 0 ⟨le_rfl,by norm_num⟩)
  simpa only [GammaPrime,curvatureMoment2_initial] using
    GammaPrime_eq_one_on_support_interval β hβ.ne' μ hmin q hq hq1 hsupp 0 ⟨le_rfl,hq.le⟩

/-- The paper's exact origin density, with a genuine right derivative at
zero already supplied by the closed-interval smoothness theorem. -/
theorem parisiSmoothDensity_initial_of_support_interval
    (β : ℝ) (hβ : 0 < β) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    parisiSmoothDensity β μ q 0 = β ^ 5 * parisiSpatialJet β μ 4 0 0 ^ 2 / 2 := by
  rw [parisiSmoothDensity_eq_moment_formula_of_support_interval β hβ.ne' μ hmin
    q hq hq1 hsupp 0 ⟨le_rfl,hq.le⟩, momentQuotient_initial_zero]
  simp only [mul_zero,zero_mul,zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,add_zero,
    quotientFourthSquarePolynomial,quotientFourthSquared_initial,quotientDenominator_initial]
  rw [parisiHessian_initial_of_support_interval β hβ μ hmin q hq hq1 hsupp]
  exact quotient_density_at_zero β _ hβ.ne'

end FRSB
