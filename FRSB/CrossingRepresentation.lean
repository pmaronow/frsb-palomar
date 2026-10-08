module

public import FRSB.CrossingWeightLaw
public import FRSB.CrossingShape

@[expose] public section

/-! Analytic core of the normalized transport/IBP argument. The weight law
 is an actual measure, its covariance is an actual Bochner integral, and
 the vanishing boundary terms are checked by the improper FTC. Specializing
 the transport and decay inputs to the actual forward/backward PDE remains
 a separate step. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FRSB

/-- Differentiating a normalized weighted mean after its numerator and
 denominator have been differentiated under the integral. -/
theorem crossing_normalized_transport_hasDerivAt
    (ω Φ : ℝ → ℝ → ℝ) (S L : ℝ → ℝ) (t : ℝ)
    (hω : IntegrableOn (ω t) (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω t x)
    (hN : HasDerivAt (fun r => ∫ x in Ioi (0 : ℝ), Φ r x * ω r x)
      (∫ x in Ioi (0 : ℝ), S x * ω t x) t)
    (hZ : HasDerivAt (fun r => crossingWeightMass (ω r))
      (∫ x in Ioi (0 : ℝ), L x * ω t x) t) :
    HasDerivAt (fun r => (∫ x in Ioi (0 : ℝ), Φ r x * ω r x) /
        crossingWeightMass (ω r))
      ((∫ x, S x ∂crossingWeightLaw (ω t)) -
        (∫ x, Φ t x ∂crossingWeightLaw (ω t)) *
        (∫ x, L x ∂crossingWeightLaw (ω t))) t := by
  have hnonzero := (crossingWeightMass_pos (ω t) hω hp).ne'
  convert hN.div hZ hnonzero using 1
  rw [integral_crossingWeightLaw (ω t) S hω hp,
    integral_crossingWeightLaw (ω t) (Φ t) hω hp,
    integral_crossingWeightLaw (ω t) L hω hp]
  field_simp

/-- Centering of Phi+Psi follows from the exact derivative of the flux W
 and its vanishing values at zero and infinity. -/
theorem crossing_centered_expectation_from_IBP (ω Φ Ψ W : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x)
    (hΦ : IntegrableOn (fun x => Φ x * ω x) (Ioi (0 : ℝ)))
    (hΨ : IntegrableOn (fun x => Ψ x * ω x) (Ioi (0 : ℝ)))
    (hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt W (-(Φ x + Ψ x) * ω x) x)
    (hW0 : W 0 = 0) (hWtop : Tendsto W atTop (𝓝 0)) :
    (∫ x, Ψ x ∂crossingWeightLaw ω) = -(∫ x, Φ x ∂crossingWeightLaw ω) := by
  have hdi : IntegrableOn (fun x => -(Φ x + Ψ x) * ω x) (Ioi (0 : ℝ)) := by
    convert (hΦ.add hΨ).neg using 1
    funext x
    simp only [Pi.neg_apply, Pi.add_apply]
    ring
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd hdi hWtop
  rw [hW0, sub_self] at hi
  have hex : (fun x => -(Φ x + Ψ x) * ω x) =
      fun x => -(Φ x * ω x + Ψ x * ω x) := by funext x; ring
  rw [hex, integral_neg, integral_add hΦ hΨ] at hi
  rw [integral_crossingWeightLaw ω Ψ hω hp, integral_crossingWeightLaw ω Φ hω hp]
  have hz : (∫ x in Ioi (0 : ℝ), Ψ x * ω x) =
      -(∫ x in Ioi (0 : ℝ), Φ x * ω x) := by linarith
  rw [hz, neg_div]

/-- The second integration by parts is performed on the actual product
 H*W, where W=omega*z. Its boundary terms give the weighted identity. -/
theorem crossing_H_expectation_from_IBP (ω Φ Ψ z H Hx : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x)
    (hR : IntegrableOn (fun x => (z x * Hx x) * ω x) (Ioi (0 : ℝ)))
    (hH : IntegrableOn (fun x => H x * (Φ x + Ψ x) * ω x) (Ioi (0 : ℝ)))
    (hdH : ∀ x ∈ Ici (0 : ℝ), HasDerivAt H (Hx x) x)
    (hdW : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => ω x * z x)
      (-(Φ x + Ψ x) * ω x) x)
    (hz0 : z 0 = 0)
    (hWtop : Tendsto (fun x => H x * (ω x * z x)) atTop (𝓝 0)) :
    (∫ x, z x * Hx x ∂crossingWeightLaw ω) =
      (∫ x, H x * (Φ x + Ψ x) ∂crossingWeightLaw ω) := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => H x * (ω x * z x))
      ((z x * Hx x) * ω x - H x * (Φ x + Ψ x) * ω x) x := by
    intro x hx
    convert (hdH x hx).mul (hdW x hx) using 1
    ring
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hR.sub hH) hWtop
  simp only [hz0, mul_zero, sub_zero] at hi
  rw [integral_sub hR hH] at hi
  rw [integral_crossingWeightLaw ω _ hω hp, integral_crossingWeightLaw ω _ hω hp]
  congr 1
  linarith

/-- Exact covariance cancellation in the positive representation. -/
theorem crossing_positive_representation_identity
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (Φ Q H K Ψ R : ℝ → ℝ)
    (f f' : ℝ) (_hΦ : Integrable Φ μ) (hQ : Integrable Q μ)
    (hH : Integrable H μ) (hK : Integrable K μ)
    (hΦK : Integrable (fun x => Φ x * K x) μ)
    (_hΦQ : Integrable (fun x => Φ x * Q x) μ)
    (hΦH : Integrable (fun x => Φ x * H x) μ)
    (hHΨ : Integrable (fun x => H x * Ψ x) μ)
    (hR : Integrable R μ)
    (hf : f = ∫ x, Φ x ∂μ)
    (hc : (∫ x, Ψ x ∂μ) = -f)
    (hIBP : (∫ x, R x ∂μ) = ∫ x, H x * (Φ x + Ψ x) ∂μ)
    (hderiv : f' = (∫ x, Q x * Φ x + R x + Φ x * (K x / 2 - Q x - H x) ∂μ) -
      f * (∫ x, K x / 2 - Q x - H x ∂μ)) :
    f' - (∫ x, Q x ∂μ) * f =
      crossingCovariance μ Φ K / 2 + crossingCovariance μ H Ψ := by
  have hHQ : Integrable (fun x => H x * Φ x) μ := by
    simpa only [mul_comm] using hΦH
  have he : (fun x => Q x * Φ x + R x + Φ x * (K x / 2 - Q x - H x)) =
      (fun x => R x + Φ x * K x / 2 - Φ x * H x) := by funext x; ring
  have heH : (fun x => H x * (Φ x + Ψ x)) =
      (fun x => H x * Φ x + H x * Ψ x) := by funext x; ring
  rw [heH, integral_add hHQ hHΨ] at hIBP
  have hRK : Integrable (fun x => R x + Φ x * K x / 2) μ := hR.add (hΦK.div_const 2)
  have hLQ : Integrable (fun x => K x / 2 - Q x) μ := (hK.div_const 2).sub hQ
  rw [hderiv, he, integral_sub hRK hΦH,
    integral_add hR (hΦK.div_const 2), integral_div,
    integral_sub hLQ hH, integral_sub (hK.div_const 2) hQ,
    integral_div, hIBP]
  have hcomm : (∫ x, H x * Φ x ∂μ) = ∫ x, Φ x * H x ∂μ := by
    congr 1
    funext x
    ring
  rw [hcomm]
  dsimp [crossingCovariance]
  rw [← hf, hc]
  ring

/-- The strict sign is now a consequence of the actual probability law,
 the two spatial order conclusions, and the exact cancellation identity. -/
theorem crossing_positive_representation_strict
    (ω Φ K H Ψ : ℝ → ℝ)
    (hω : IntegrableOn ω (Ioi (0 : ℝ))) (hp : ∀ x > 0, 0 < ω x)
    (hΦ : Integrable Φ (crossingWeightLaw ω)) (hK : Integrable K (crossingWeightLaw ω))
    (hH : Integrable H (crossingWeightLaw ω)) (hΨ : Integrable Ψ (crossingWeightLaw ω))
    (hΦK : Integrable (fun x => Φ x * K x) (crossingWeightLaw ω))
    (hHΨ : Integrable (fun x => H x * Ψ x) (crossingWeightLaw ω))
    (hmΦ : StrictMonoOn Φ (Ici 0)) (hmK : StrictMonoOn K (Ici 0))
    (hmH : MonotoneOn H (Ici 0)) (hmΨ : MonotoneOn Ψ (Ici 0)) :
    0 < crossingCovariance (crossingWeightLaw ω) Φ K / 2 +
      crossingCovariance (crossingWeightLaw ω) H Ψ := by
  have := crossingWeightLaw_isProbability ω hω hp
  have hs := crossingCovariance_pos_of_positive_weight ω Φ K hω hp hΦ hK hΦK hmΦ hmK
  have hn := crossingCovariance_nonneg _ H Ψ hH hΨ hHΨ
    (crossingWeightLaw_halfLine ω) hmH hmΨ
  linarith

/-- The forward clock t=beta^2*s contributes the additional beta^2 factor
 when differentiating Gamma''=2*beta^4*Z*f. -/
theorem hasDerivAt_crossing_second_factor (Z f : ℝ → ℝ) (β s Z' f' : ℝ)
    (hZ : HasDerivAt Z Z' (β ^ 2 * s)) (hf : HasDerivAt f f' (β ^ 2 * s)) :
    HasDerivAt (fun r => 2 * β ^ 4 * Z (β ^ 2 * r) * f (β ^ 2 * r))
      (2 * β ^ 6 * (Z' * f (β ^ 2 * s) + Z (β ^ 2 * s) * f')) s := by
  have ht := (hasDerivAt_id s).const_mul (β ^ 2)
  have hz := hZ.comp s ht
  have hff := hf.comp s ht
  convert (hz.const_mul (2 * β ^ 4)).mul hff using 1
  · funext r
    simp only [Function.comp_apply, Pi.mul_apply]
  · simp only [Function.comp_apply]
    ring

theorem crossing_second_factor_zero_iff (β Z f : ℝ) (hβ : β ≠ 0) (hZ : 0 < Z) :
    2 * β ^ 4 * Z * f = 0 ↔ f = 0 := by
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 4 hβ)) hZ.ne'))

/-- At a zero of Gamma'', the positive representation yields the actual
 strictly positive derivative of its rescaled factor. -/
theorem crossing_second_factor_derivative_pos_at_zero (β Z Z' f f' q : ℝ)
    (hβ : β ≠ 0) (hZ : 0 < Z) (hzero : 2 * β ^ 4 * Z * f = 0)
    (hrep : 0 < f' - q * f) : 0 < 2 * β ^ 6 * (Z' * f + Z * f') := by
  have hf := (crossing_second_factor_zero_iff β Z f hβ hZ).mp hzero
  simp only [hf, mul_zero, zero_add, sub_zero] at hrep ⊢
  have hb6 : 0 < β ^ 6 := by positivity
  exact mul_pos (mul_pos (by norm_num) hb6) (mul_pos hZ hrep)

end FRSB
