module

public import FRSB.CrossingThirdIBP

@[expose] public section

/-! A second exact score-flux identity fixes the averaged transport
coefficient. This supplies the full positive representation at every time. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

theorem integrable_bridgeCrossingQ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => backwardQ β μ (parisiCDF μ s) (s,x))
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  let := bridgeCrossingWeightLaw_isProbability β hβ μ s hs
  apply (integrable_const (1 : ℝ)).mono'
    ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_backwardQ β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩).continuousAt).aestronglyMeasurable)
  exact .of_forall fun x => by
    simpa only [Real.norm_eq_abs] using backwardQ_abs_le_one_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩

theorem bridge_crossing_coefficient_centering (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∫ x, bridgeCrossingK β μ s hs x ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs))/2 -
      (∫ x, backwardQ β μ (parisiCDF μ s) (s,x) ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) -
      (∫ x, backwardH β μ (parisiCDF μ s) (s,x) ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
        2 * ∫ x, actualCrossingPhi β μ (parisiCDF μ s) (s,x)
          ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs) := by
  let w := bridgeCrossingWeight β μ s hs
  let a := fun x => bridgeCrossingK β μ s hs x / 2 - backwardQ β μ (parisiCDF μ s) (s,x) -
    backwardH β μ (parisiCDF μ s) (s,x) - 2*actualCrossingPhi β μ (parisiCDF μ s) (s,x)
  let b := fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x) + bridgeCrossingPsi β μ s hs x
  have hw := bridgeCrossingWeight_integrable β hβ μ s hs
  have hp := fun x (_ : 0 < x) => bridgeCrossingWeight_pos β hβ μ s hs x
  have hK := integrable_bridgeCrossingK β hβ μ s hs
  have hQ := integrable_bridgeCrossingQ β hβ μ s hs
  have hH := integrable_bridgeCrossingH β hβ μ s hs
  have hPhi := integrable_bridgeCrossingPhi β hβ μ s hs
  have hPsi := integrable_bridgeCrossingPsi β hβ μ s hs
  have ha : Integrable a (crossingWeightLaw w) := ((hK.div_const 2).sub hQ |>.sub hH).sub (hPhi.const_mul 2)
  have hb : Integrable b (crossingWeightLaw w) := hPhi.add hPsi
  have haw := integrable_weighted_of_crossingWeightLaw w a hw hp ha
  have hbw := integrable_weighted_of_crossingWeightLaw w b hw hp hb
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun y => bridgeCrossingN β μ s hs y*w y) ((-2*a x-3*b x)*w x) x := by
    intro x _
    have h := (hasDerivAt_bridgeCrossingN β hβ μ s hs x).mul
      (hasDerivAt_bridgeCrossingWeight β hβ μ s hs x)
    convert h using 1
    dsimp [a,b,bridgeCrossingK,crossingK,bridgeCrossingPsi,actualCrossingPhi,crossingPhi,
      backwardH,backwardHJet,backwardQ,backwardQJet,w,backwardZ]
    ring
  have htop : Tendsto (fun x => bridgeCrossingN β μ s hs x*w x) atTop (𝓝 0) := by
    apply tendsto_zero_of_crossingGaussianEnvelope_bound _ (β^2*s) 1
      (2*((β^2*s)⁻¹+3)*Real.exp (β^2)*(Real.sqrt (2*Real.pi*(β^2*s)))⁻¹)
      (mul_pos (sq_pos_of_ne_zero hβ) hs.1)
    intro x hx
    rw [norm_mul]
    have hN : ‖bridgeCrossingN β μ s hs x‖ ≤ ((β^2*s)⁻¹+3)*(1+|x|) := by
      apply (norm_bridgeCrossingN_linear β hβ μ s hs x).trans
      rw [div_eq_mul_inv]
      nlinarith [inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le,abs_nonneg x]
    apply (mul_le_mul hN (bridgeCrossingWeight_gaussian_envelope β hβ μ s hs x hx)
      (norm_nonneg _) (by have hv := mul_pos (sq_pos_of_ne_zero hβ) hs.1; positivity)).trans_eq
    unfold crossingGaussianEnvelope
    simp only [pow_zero,pow_one]
    ring
  have hdi : IntegrableOn (fun x => (-2*a x-3*b x)*w x) (Ioi (0 : ℝ)) := by
    have he : (fun x => (-2*a x-3*b x)*w x) =
        (fun x => (-2)*(a x*w x)) - (fun x => 3*(b x*w x)) := by funext x; dsimp; ring
    rw [he]
    exact (haw.const_mul (-2)).sub (hbw.const_mul 3)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd hdi htop
  rw [bridgeCrossingN_origin β hβ μ s hs,zero_mul,sub_self] at hi
  have hex : (fun x => (-2*a x-3*b x)*w x) = fun x => (-2)*(a x*w x)-3*(b x*w x) := by
    funext x;ring
  rw [hex,integral_sub (haw.const_mul (-2)) (hbw.const_mul 3),integral_const_mul,integral_const_mul] at hi
  have hPsiMean := bridge_crossing_centering β hβ μ s hs
  have hbMean : (∫ x,b x ∂crossingWeightLaw w)=0 := by
    change (∫ x,actualCrossingPhi β μ (parisiCDF μ s) (s,x)+
      bridgeCrossingPsi β μ s hs x ∂crossingWeightLaw w)=0
    rw [integral_add hPhi hPsi,hPsiMean]
    ring
  have hbZero : (∫ x in Ioi (0 : ℝ),b x*w x)=0 := by
    rw [integral_crossingWeightLaw w b hw hp] at hbMean
    exact (div_eq_zero_iff.mp hbMean).resolve_right (crossingWeightMass_pos w hw hp).ne'
  have haZero : (∫ x,a x ∂crossingWeightLaw w)=0 := by
    rw [integral_crossingWeightLaw w a hw hp]
    have hzero : (∫ x in Ioi (0 : ℝ),a x*w x)=0 := by rw [hbZero,mul_zero,sub_zero] at hi;linarith
    rw [hzero,zero_div]
  have ho := integral_sub (((hK.div_const 2).sub hQ).sub hH) (hPhi.const_mul 2)
  have hh := integral_sub ((hK.div_const 2).sub hQ) hH
  have hq := integral_sub (hK.div_const 2) hQ
  simp only [Pi.sub_apply] at ho hh hq
  change (∫ x,bridgeCrossingK β μ s hs x/2-backwardQ β μ (parisiCDF μ s) (s,x)-
    backwardH β μ (parisiCDF μ s) (s,x)-2*actualCrossingPhi β μ (parisiCDF μ s) (s,x)
      ∂crossingWeightLaw w)=0 at haZero
  rw [ho,hh,hq,integral_div,integral_const_mul] at haZero
  linarith

end FRSB
