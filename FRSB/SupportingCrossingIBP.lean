module

public import FRSB.CrossingPositiveRepresentation

@[expose] public section

/-! Actual individual H-weight integration by parts and covariance display. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

theorem integrable_bridgeCrossing_z_Hx (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) :
    Integrable (fun x=>backwardZ β μ (s,x)*backwardHx β μ (parisiCDF μ s) (s,x))
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  let := bridgeCrossingWeightLaw_isProbability β hβ μ s hs
  have hc := backward_fields_smooth β hβ μ (parisiCDF μ s) s ⟨hs.1.le,hs.2⟩
  apply (integrable_const (6:ℝ)).mono'
    (hc.1.continuous.mul hc.2.2.2.2.2.continuous).aestronglyMeasurable
  exact .of_forall fun x=>by
    simp only [Pi.mul_apply,norm_mul]
    have hz : ‖backwardZ β μ (s,x)‖≤1 := by
      simpa only [Real.norm_eq_abs] using (backward_fields_bounded β hβ μ s x ⟨hs.1.le,hs.2⟩).1
    have hHx : ‖backwardHx β μ (parisiCDF μ s) (s,x)‖≤6 := by
      simpa only [Real.norm_eq_abs] using (backward_fields_bounded β hβ μ s x ⟨hs.1.le,hs.2⟩).2.2.2.1
    nlinarith [norm_nonneg (backwardZ β μ (s,x)),norm_nonneg (backwardHx β μ (parisiCDF μ s) (s,x))]

theorem integrable_bridgeCrossingH_mul_Phi (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) :
    Integrable (fun x=>backwardH β μ (parisiCDF μ s) (s,x)*actualCrossingPhi β μ (parisiCDF μ s) (s,x))
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) :=
  (integrable_bridgeCrossingPhi β hβ μ s hs).bdd_mul
    ((backward_fields_smooth β hβ μ (parisiCDF μ s) s ⟨hs.1.le,hs.2⟩).2.2.2.2.1.continuous.aestronglyMeasurable)
    (.of_forall fun x=>norm_backwardH_le_four_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩)

theorem actual_crossing_H_IBP (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) 1) :
    (∫ x,backwardZ β μ (s,x)*backwardHx β μ (parisiCDF μ s) (s,x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
    (∫ x,backwardH β μ (parisiCDF μ s) (s,x)*
      (actualCrossingPhi β μ (parisiCDF μ s) (s,x)+bridgeCrossingPsi β μ s hs x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) ∧
    (∫ x,backwardH β μ (parisiCDF μ s) (s,x)*
      (actualCrossingPhi β μ (parisiCDF μ s) (s,x)+bridgeCrossingPsi β μ s hs x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) =
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s hs))
      (fun x=>backwardH β μ (parisiCDF μ s) (s,x))
      (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x))+
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s hs))
      (fun x=>backwardH β μ (parisiCDF μ s) (s,x)) (bridgeCrossingPsi β μ s hs) := by
  let w := bridgeCrossingWeight β μ s hs
  have hw := bridgeCrossingWeight_integrable β hβ μ s hs
  have hp := fun x (_:0<x)=>bridgeCrossingWeight_pos β hβ μ s hs x
  have hR := integrable_bridgeCrossing_z_Hx β hβ μ s hs
  have hPhi := integrable_bridgeCrossingH_mul_Phi β hβ μ s hs
  have hPsi := integrable_bridgeCrossingH_mul_Psi β hβ μ s hs
  have he : (fun x=>backwardH β μ (parisiCDF μ s) (s,x)*
      (actualCrossingPhi β μ (parisiCDF μ s) (s,x)+bridgeCrossingPsi β μ s hs x)) =
    (fun x=>backwardH β μ (parisiCDF μ s) (s,x)*actualCrossingPhi β μ (parisiCDF μ s) (s,x))+
      (fun x=>backwardH β μ (parisiCDF μ s) (s,x)*bridgeCrossingPsi β μ s hs x) := by
    funext x;dsimp only [Pi.add_apply];ring
  have hcomb : Integrable (fun x=>backwardH β μ (parisiCDF μ s) (s,x)*
      (actualCrossingPhi β μ (parisiCDF μ s) (s,x)+bridgeCrossingPsi β μ s hs x))
      (crossingWeightLaw w) := by rw [he];exact hPhi.add hPsi
  have hRW := integrable_weighted_of_crossingWeightLaw w _ hw hp hR
  have hHW := integrable_weighted_of_crossingWeightLaw w _ hw hp hcomb
  have htop : Tendsto (fun x=>backwardH β μ (parisiCDF μ s) (s,x)*(w x*backwardZ β μ (s,x)))
      atTop (𝓝 0) := by
    apply tendsto_zero_of_crossingGaussianEnvelope_bound _ (β^2*s) 0
      (4*Real.exp (β^2)*(Real.sqrt (2*Real.pi*(β^2*s)))⁻¹)
      (mul_pos (sq_pos_of_ne_zero hβ) hs.1)
    intro x hx
    rw [norm_mul,norm_mul]
    have hH := norm_backwardH_le_four_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩
    have hz : ‖backwardZ β μ (s,x)‖≤1 := by
      simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩
    calc
      _ ≤ 4*(‖w x‖*1) := by gcongr
      _ ≤ 4*(Real.exp (β^2)*(Real.sqrt (2*Real.pi*(β^2*s)))⁻¹*crossingGaussianEnvelope (β^2*s) 0 x) := by
        simp only [mul_one]
        exact mul_le_mul_of_nonneg_left (bridgeCrossingWeight_gaussian_envelope β hβ μ s hs x hx) (by norm_num)
      _ = _ := by ring
  refine ⟨crossing_H_expectation_from_IBP w
    (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x)) (bridgeCrossingPsi β μ s hs)
    (fun x=>backwardZ β μ (s,x)) (fun x=>backwardH β μ (parisiCDF μ s) (s,x))
    (fun x=>backwardHx β μ (parisiCDF μ s) (s,x)) hw hp hRW hHW
    (fun x _=>hasDerivAt_backwardH β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩)
    (fun x _=>hasDerivAt_bridgeCrossingWeight_mul_z β hβ μ s hs x)
    (backwardZ_at_zero β μ s ⟨hs.1.le,hs.2⟩) htop,?_⟩
  have hadd := integral_add hPhi hPsi
  rw [he]
  change (∫ x,backwardH β μ (parisiCDF μ s) (s,x)*actualCrossingPhi β μ (parisiCDF μ s) (s,x)+
    backwardH β μ (parisiCDF μ s) (s,x)*bridgeCrossingPsi β μ s hs x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs))=_
  rw [hadd]
  unfold crossingCovariance
  dsimp only [Pi.add_apply]
  rw [bridge_crossing_centering β hβ μ s hs]
  ring

/-- The intermediate normalized transport display, before the Q and H
covariances are cancelled. All fields and the probability law are actual. -/
theorem actual_crossing_mean_transport (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    (m a b : ℝ) (hI : Ioo a b⊆Ioo (0:ℝ) 1)
    (hc : ∀s∈Ioo a b,parisiCDF μ s=m) {s : ℝ} (hs : s∈Ioo a b) :
    let ht : s∈Ioc (0:ℝ) 1 := ⟨(hI hs).1,(hI hs).2.le⟩
    let ρ := crossingWeightLaw (bridgeCrossingWeight β μ s ht)
    let Φ := fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x)
    let Q := fun x=>backwardQ β μ (parisiCDF μ s) (s,x)
    let H := fun x=>backwardH β μ (parisiCDF μ s) (s,x)
    let K := bridgeCrossingK β μ s ht
    let R := fun x=>backwardZ β μ (s,x)*backwardHx β μ (parisiCDF μ s) (s,x)
    deriv (crossingForwardMeanPhi β μ) (β^2*s) =
      (∫ x,Q x*Φ x+R x ∂ρ)+crossingCovariance ρ Φ (fun x=>K x/2-Q x-H x) := by
  dsimp only
  let ht : s∈Ioc (0:ℝ) 1 := ⟨(hI hs).1,(hI hs).2.le⟩
  let ρ := crossingWeightLaw (bridgeCrossingWeight β μ s ht)
  let Φ := fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x)
  let Q := fun x=>backwardQ β μ (parisiCDF μ s) (s,x)
  let H := fun x=>backwardH β μ (parisiCDF μ s) (s,x)
  let K := bridgeCrossingK β μ s ht
  let Ψ := bridgeCrossingPsi β μ s ht
  let R := fun x=>backwardZ β μ (s,x)*backwardHx β μ (parisiCDF μ s) (s,x)
  change deriv (crossingForwardMeanPhi β μ) (β^2*s)=
    (∫ x,Q x*Φ x+R x ∂ρ)+crossingCovariance ρ Φ (fun x=>K x/2-Q x-H x)
  have hΦ := integrable_bridgeCrossingPhi β hβ μ s ht
  have hQ := integrable_bridgeCrossingQ β hβ μ s ht
  have hH := integrable_bridgeCrossingH β hβ μ s ht
  have hK := integrable_bridgeCrossingK β hβ μ s ht
  have hΦK := integrable_bridgeCrossingPhi_mul_K β hβ μ s ht
  have hHΦ := integrable_bridgeCrossingH_mul_Phi β hβ μ s ht
  have hR := integrable_bridgeCrossing_z_Hx β hβ μ s ht
  have hQΦ : Integrable (fun x=>Q x*Φ x) ρ := by
    have hh := hΦ.bdd_mul
      ((continuous_iff_continuousAt.mpr fun x=>
        (hasDerivAt_backwardQ β hβ μ (parisiCDF μ s) s x ⟨ht.1.le,ht.2⟩).continuousAt).aestronglyMeasurable)
      (.of_forall fun x=>by
        simpa only [Real.norm_eq_abs] using
          backwardQ_abs_le_one_crossing β hβ μ s x ⟨ht.1.le,ht.2⟩)
    exact hh
  have hRIBP : (∫ x,R x ∂ρ)=crossingCovariance ρ H Φ+crossingCovariance ρ H Ψ :=
    (actual_crossing_H_IBP β hβ μ s ht).1.trans (actual_crossing_H_IBP β hβ μ s ht).2
  have hd := hasDerivAt_crossingMeanPhi_positive_representation β hβ μ m a b hI hc hs
  have he : β^2*s/β^2=s := mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ)
  have hcomp := hd.comp_of_eq (β^2*s) ((hasDerivAt_id (β^2*s)).div_const (β^2)) he.symm
  have hder : deriv (crossingForwardMeanPhi β μ) (β^2*s)=
      (∫ x,Q x ∂ρ)*(∫ x,Φ x ∂ρ)+crossingCovariance ρ Φ K/2+crossingCovariance ρ H Ψ := by
    rw [←crossingMeanPhi_eq_expectation β hβ μ s ht]
    convert hcomp.deriv using 1
    · rfl
    · field_simp [hβ]
      dsimp only [Q,ρ,Φ,H,K,Ψ]
      ring
  rw [hder,integral_add hQΦ hR,hRIBP]
  have hp : (fun x=>Φ x*(K x/2-Q x-H x))=
      fun x=>Φ x*K x/2-Q x*Φ x-H x*Φ x := by funext x;ring
  have hL : (∫ x,Φ x*K x/2-Q x*Φ x-H x*Φ x ∂ρ)=
      (∫ x,Φ x*K x ∂ρ)/2-(∫ x,Q x*Φ x ∂ρ)-(∫ x,H x*Φ x ∂ρ) := by
    calc
      _ = (∫ x,Φ x*K x/2-Q x*Φ x ∂ρ)-(∫ x,H x*Φ x ∂ρ) :=
        integral_sub ((hΦK.div_const 2).sub hQΦ) hHΦ
      _ = _ := by rw [integral_sub (hΦK.div_const 2) hQΦ,integral_div]
  have hJ : (∫ x,K x/2-Q x-H x ∂ρ)=
      (∫ x,K x ∂ρ)/2-(∫ x,Q x ∂ρ)-(∫ x,H x ∂ρ) := by
    calc
      _ = (∫ x,K x/2-Q x ∂ρ)-(∫ x,H x ∂ρ) :=
        integral_sub ((hK.div_const 2).sub hQ) hH
      _ = _ := by rw [integral_sub (hK.div_const 2) hQ,integral_div]
  unfold crossingCovariance
  rw [hp,hL,hJ]
  ring

end FRSB
