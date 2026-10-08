module

public import FRSB.CrossingActualDecay
public import FRSB.CrossingTransportBundle

@[expose] public section

/-! Literal Lemma 5.4 in the forward clock, including the actual time
 derivatives, all bounded transported fields, and origin flux conditions. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

theorem crossing_decay (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤1)
    (hc : ∀s∈Ico a b,parisiCDF μ s=m) (l u : ℝ)
    (hla : a<l) (_hlu : l≤u) (hub : u<b) :
    ∃ c : ℝ,0<c ∧ ∀s∈Icc l u,∀x:ℝ,0≤x→
      crossingForwardField β (fun p=>crossingPhysicalWeight β μ p.1 p.2) (β^2*s,x)+
        ‖deriv (fun t=>crossingForwardField β (fun p=>crossingPhysicalWeight β μ p.1 p.2) (t,x)) (β^2*s)‖+
        ‖deriv (fun t=>crossingForwardField β
          (fun p=>actualCrossingPhi β μ m p*crossingPhysicalWeight β μ p.1 p.2) (t,x)) (β^2*s)‖ ≤
      c*(1+x^2)*Real.exp (x-x^2/(2*β^2)) := by
  refine ⟨crossingClockDecayConstant β l,crossingClockDecayConstant_pos β hβ l,?_⟩
  intro s hs x hx
  have hsab : s∈Ioo a b := ⟨hla.trans_le hs.1,hs.2.trans_lt hub⟩
  have hs1 : s∈Icc l 1 := ⟨hs.1,hs.2.trans (hub.le.trans hb)⟩
  have hm : parisiCDF μ s=m := hc s ⟨hsab.1.le,hsab.2⟩
  have hclock : β^2*s/β^2=s := mul_div_cancel_left₀ s (pow_ne_zero 2 hβ)
  have hw := hasDerivAt_crossingForwardField_time β hβ
    (fun p=>crossingPhysicalWeight β μ p.1 p.2) s x (crossingPhysicalWeightT β μ m s x)
    (hasDerivAt_crossingPhysicalWeight_time β hβ μ ha hab hb hc hsab x)
  have hPhiw := hasDerivAt_crossingForwardField_time β hβ
    (fun p=>actualCrossingPhi β μ m p*crossingPhysicalWeight β μ p.1 p.2) s x
    (crossingPhysicalPhiWeightT β μ m s x)
    (hasDerivAt_crossingPhysicalPhiWeight_time β hβ μ ha hab hb hc hsab x)
  rw [hw.deriv,hPhiw.deriv]
  simp only [crossingForwardField,hclock]
  rw [←hm]
  have hbound := crossing_actual_clock_source_decay_bound β hβ μ l (ha.trans_lt hla) hs1 hx
  convert hbound using 1
  unfold crossingGaussianEnvelope
  rw [sq_abs]
  ring

theorem crossing_bounded_transport_fields (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤1)
    (hc : ∀s∈Ico a b,parisiCDF μ s=m) {s : ℝ} (hs : s∈Ioo a b) (x : ℝ) (hx : 0≤x) :
    ‖actualCrossingVelocity β μ m (s,x)‖≤2 ∧
    ‖backwardZ β μ (s,x)‖≤1 ∧
    ‖actualCrossingPhi β μ m (s,x)‖≤3 ∧
    ‖deriv (fun y=>actualCrossingPhi β μ m (s,y)) x‖≤10 ∧
    ‖crossingMaterialDerivative β μ m (actualCrossingPhi β μ m) s x‖≤9 ∧
    ‖backwardH β μ m (s,x)‖≤4 ∧
    actualCrossingVelocity β μ m (s,0)=0 ∧ backwardZ β μ (s,0)=0 := by
  have ht : s∈Icc (0:ℝ) 1 := ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩
  have hm : parisiCDF μ s=m := hc s ⟨hs.1.le,hs.2⟩
  have h := crossing_actual_bounded_fields β hβ μ s x ht hx
  have hz := crossing_actual_origin β hβ μ s ht
  rw [(hasDerivAt_actualCrossingPhi β hβ μ m s x ht).deriv,
    (crossing_transport β hβ μ ha hab hb hc hs x).2.2.2.1,←hm]
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,hz⟩

end FRSB
