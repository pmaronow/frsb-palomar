module

public import FRSB.CrossMomentTransfer
public import FRSB.CrossingCoefficientCentering

@[expose] public section

/-! The full positive crossing representation at every constant-mass time.
It is derived from the genuine polynomial moment hierarchy and two exact
spatial score fluxes. The formula uses precisely the normalized bridge law. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

def crossingMeanPhi (β : ℝ) (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  GammaSecond β μ s / (2*β^4*curvatureMoment2 β μ s)

def crossingForwardMeanPhi (β : ℝ) (μ : ParisiMeasure) (t : ℝ) : ℝ :=
  crossingMeanPhi β μ (t/β^2)

theorem crossingMeanPhi_eq_expectation (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    crossingMeanPhi β μ s = ∫ x,actualCrossingPhi β μ (parisiCDF μ s) (s,x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs) := by
  rw [integral_crossingPhi_eq_GammaSecond β hβ μ s hs,
    crossingWeightMass_bridge_eq_curvatureMoment2 β hβ μ s hs]
  rfl

theorem hasDerivAt_crossingMeanPhi_source (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (m a b : ℝ) (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hc : ∀ s ∈ Ioo a b,parisiCDF μ s=m) {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (crossingMeanPhi β μ)
      (β^2*((∫ x,bridgeCrossingThirdSource β μ s x
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))-
          2*crossingMeanPhi β μ s^2)) s := by
  have ht : s ∈ Ioc (0 : ℝ) 1 := ⟨(hI hs).1,(hI hs).2.le⟩
  have hZ := (hasDerivAt_GammaPrime_of_constant_CDF β hβ μ m a b hI hc hs).div_const (β^2)
  have he : (fun r=>GammaPrime β μ r/β^2)=curvatureMoment2 β μ := by
    funext r
    unfold GammaPrime
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ)
  rw [he] at hZ
  have hd := (hasDerivAt_GammaSecond_of_constant_CDF β hβ μ m a b hI hc hs).div
    (hZ.const_mul (2*β^4))
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hβ))
      (curvatureMoment2_pos β hβ μ ⟨ht.1.le,ht.2⟩).ne')
  convert hd using 1
  · rfl
  · rw [integral_crossingThirdSource_eq_GammaThird β hβ μ s ht,
      crossingWeightMass_bridge_eq_curvatureMoment2 β hβ μ s ht,hc s hs]
    dsimp only [crossingMeanPhi]
    field_simp [hβ,(curvatureMoment2_pos β hβ μ ⟨ht.1.le,ht.2⟩).ne']

theorem bridge_crossing_source_covariance_identity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ x,bridgeCrossingThirdSource β μ s x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs))-
      2*crossingMeanPhi β μ s^2-
      (∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs))*crossingMeanPhi β μ s =
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s hs))
      (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x)) (bridgeCrossingK β μ s hs)/2+
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s hs))
      (fun x=>backwardH β μ (parisiCDF μ s) (s,x)) (bridgeCrossingPsi β μ s hs) := by
  have hf := crossingMeanPhi_eq_expectation β hβ μ s hs
  have hpsi := bridge_crossing_centering β hβ μ s hs
  have hcoef := bridge_crossing_coefficient_centering β hβ μ s hs
  have hsrc := bridge_crossing_third_source_expectation β hβ μ s hs
  have hadd := integral_add ((integrable_bridgeCrossingPhi_mul_K β hβ μ s hs).div_const 2)
    (integrable_bridgeCrossingH_mul_Psi β hβ μ s hs)
  rw [hadd,integral_div] at hsrc
  rw [hsrc,hf]
  unfold crossingCovariance
  rw [hpsi]
  dsimp only
  linear_combination (∫ x,actualCrossingPhi β μ (parisiCDF μ s) (s,x)
    ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs))*hcoef

/-- Exact formula in physical overlap time. -/
theorem hasDerivAt_crossingMeanPhi_positive_representation (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (m a b : ℝ) (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hc : ∀ s ∈ Ioo a b,parisiCDF μ s=m) {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (crossingMeanPhi β μ)
      (β^2*((∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))*crossingMeanPhi β μ s+
        crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
          (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x))
          (bridgeCrossingK β μ s ⟨(hI hs).1,(hI hs).2.le⟩)/2+
        crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
          (fun x=>backwardH β μ (parisiCDF μ s) (s,x))
          (bridgeCrossingPsi β μ s ⟨(hI hs).1,(hI hs).2.le⟩))) s := by
  have hd := hasDerivAt_crossingMeanPhi_source β hβ μ m a b hI hc hs
  convert hd using 1
  have he := bridge_crossing_source_covariance_identity β hβ μ s ⟨(hI hs).1,(hI hs).2.le⟩
  linear_combination -(β^2)*he

/-- Literal paper-clock representation, including its strict sign at every
 time, rather than only at a zero of the second Gamma derivative. -/
theorem crossing_forward_positive_representation (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (m a b : ℝ) (hm : 0 < m)
    (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hc : ∀ s ∈ Ioo a b,parisiCDF μ s=m) {s : ℝ} (hs : s ∈ Ioo a b) :
    deriv (crossingForwardMeanPhi β μ) (β^2*s)-
      (∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))*crossingMeanPhi β μ s =
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
      (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x))
      (bridgeCrossingK β μ s ⟨(hI hs).1,(hI hs).2.le⟩)/2+
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
      (fun x=>backwardH β μ (parisiCDF μ s) (s,x))
      (bridgeCrossingPsi β μ s ⟨(hI hs).1,(hI hs).2.le⟩) ∧
    0 < deriv (crossingForwardMeanPhi β μ) (β^2*s)-
      (∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))*crossingMeanPhi β μ s := by
  have hd := hasDerivAt_crossingMeanPhi_positive_representation β hβ μ m a b hI hc hs
  have ht : (β^2*s)/β^2=s := mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ)
  have hcomp := hd.comp_of_eq (β^2*s) ((hasDerivAt_id (β^2*s)).div_const (β^2)) ht.symm
  have hder : deriv (crossingForwardMeanPhi β μ) (β^2*s)=
      ((∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))*crossingMeanPhi β μ s+
        crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
          (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x))
          (bridgeCrossingK β μ s ⟨(hI hs).1,(hI hs).2.le⟩)/2+
        crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
          (fun x=>backwardH β μ (parisiCDF μ s) (s,x))
          (bridgeCrossingPsi β μ s ⟨(hI hs).1,(hI hs).2.le⟩)) := by
    convert hcomp.deriv using 1
    · rfl
    · field_simp [hβ]
  constructor
  · rw [hder]
    ring
  · rw [hder]
    have hp := bridge_crossing_positive_covariances β hβ μ s ⟨(hI hs).1,(hI hs).2.le⟩
      (by rw [hc s hs];exact hm)
    linarith

end FRSB
