module

public import FRSB.CrossingDecay
public import FRSB.CrossingRepresentation

@[expose] public section

/-! Domination and boundary cancellation for the transport integrals.
The analytic inputs are actual pointwise derivatives and a concrete
Gaussian envelope, rather than an assumed derivative of an expectation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB

theorem crossing_integral_transport_flux (D S W : ℝ → ℝ)
    (hD : IntegrableOn D (Ioi (0 : ℝ))) (hS : IntegrableOn S (Ioi (0 : ℝ)))
    (hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt W (S x - D x) x)
    (hW0 : W 0 = 0) (hWtop : Tendsto W atTop (𝓝 0)) :
    (∫ x in Ioi (0 : ℝ), D x) = ∫ x in Ioi (0 : ℝ), S x := by
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd (hS.sub hD) hWtop
  rw [hW0, sub_self, integral_sub hS hD] at hi
  linarith

/-- Differentiation under the genuine half-line integral followed by
 the zero-flux cancellation of its transport term. -/
theorem crossing_integral_transport_hasDerivAt
    (F Ft : ℝ → ℝ → ℝ) (S W : ℝ → ℝ) (t : ℝ) (J : Set ℝ)
    (hJ : J ∈ 𝓝 t) (v : ℝ) (n : ℕ) (c : ℝ) (hv : 0 < v)
    (hFmeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (F r) (volume.restrict (Ioi (0 : ℝ))))
    (hFint : IntegrableOn (F t) (Ioi (0 : ℝ)))
    (hFtmeas : AEStronglyMeasurable (Ft t) (volume.restrict (Ioi (0 : ℝ))))
    (hbound : ∀ x > 0, ∀ r ∈ J, ‖Ft r x‖ ≤ c * crossingGaussianEnvelope v n x)
    (hdiff : ∀ x > 0, ∀ r ∈ J, HasDerivAt (fun u => F u x) (Ft r x) r)
    (hS : IntegrableOn S (Ioi (0 : ℝ)))
    (hflux : ∀ x ∈ Ici (0 : ℝ), HasDerivAt W (S x - Ft t x) x)
    (hW0 : W 0 = 0) (hWtop : Tendsto W atTop (𝓝 0)) :
    HasDerivAt (fun r => ∫ x in Ioi (0 : ℝ), F r x)
      (∫ x in Ioi (0 : ℝ), S x) t := by
  have hb : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ r ∈ J, ‖Ft r x‖ ≤ c * crossingGaussianEnvelope v n x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x hx
  have hd : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ r ∈ J, HasDerivAt (fun u => F u x) (Ft r x) r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hdiff x hx
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ hFmeas hFint hFtmeas
    hb ((integrable_crossingGaussianEnvelope v n hv).integrableOn.const_mul c) hd
  have he := crossing_integral_transport_flux (Ft t) S W hi.1 hS hflux hW0 hWtop
  rw [he] at hi
  exact hi.2

end FRSB
