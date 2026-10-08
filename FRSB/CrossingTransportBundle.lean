module

public import FRSB.CrossingActualTime
public import FRSB.CrossingActualWeightTime

@[expose] public section

/-! All literal transport identities of Lemma 5.2, with the actual
forward clock t = beta squared times s made explicit. -/
noncomputable section
open Set Paper
namespace FRSB
set_option maxHeartbeats 1000000

def crossingForwardField (β : ℝ) (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  f (p.1 / β ^ 2,p.2)

theorem hasDerivAt_crossingForwardField_time (β : ℝ) (hβ : β ≠ 0)
    (f : ℝ × ℝ → ℝ) (s x d : ℝ)
    (hd : HasDerivAt (fun r => f (r,x)) d s) :
    HasDerivAt (fun t => crossingForwardField β f (t,x)) (d / β ^ 2) (β ^ 2 * s) := by
  have he : β ^ 2 * s / β ^ 2 = s := mul_div_cancel_left₀ s (pow_ne_zero 2 hβ)
  have hd' : HasDerivAt (fun r => f (r,x)) d ((fun t : ℝ => t / β ^ 2) (β ^ 2 * s)) := by
    simpa only [he] using hd
  have hh := hd'.comp (β ^ 2 * s) ((hasDerivAt_id (β ^ 2 * s)).div_const (β ^ 2))
  convert hh using 1 <;> first | rfl | ring

def crossingMaterialDerivative (β : ℝ) (μ : ParisiMeasure) (m : ℝ)
    (f : ℝ × ℝ → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => f (r,x)) s / β ^ 2 +
    actualCrossingVelocity β μ m (s,x) * deriv (fun y => f (s,y)) x

theorem divide_transport (k A V R : ℝ) (hk : k ≠ 0)
    (hh : A+k*V=k*R) : A/k+V=R := by
  calc
    A/k+V = (A+k*V)/k := by field_simp
    _ = R := by rw [hh,mul_div_cancel_left₀ _ hk]

theorem actualCrossing_transport_z (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    crossingMaterialDerivative β μ m (backwardZ β μ) s x =
      backwardZ β μ (s,x) * backwardQ β μ m (s,x) -
        deriv (fun y => backwardQ β μ m (s,y)) x / 2 := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩
  have hC := (backwardC_pos β hβ μ s x ht).ne'
  unfold crossingMaterialDerivative
  rw [(hasDerivAt_backwardZ_constantCDF_time β hβ μ ha hab hb hc hs x).deriv,
    (hasDerivAt_backwardZ β hβ μ s x ht).deriv,
    (hasDerivAt_backwardQ β hβ μ m s x ht).deriv,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hβ)]
  have hh := crossing_transport_z_from_jet m (backwardB β μ (s,x)) (backwardC β μ (s,x))
    (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x)) (backwardD β μ 5 (s,x)) hC
  convert hh using 1 <;>
    (dsimp [actualCrossingVelocity,backwardZ,backwardZJet,backwardZx,backwardZxJet,
      backwardQ,backwardQJet,backwardQxJet,backwardZxxJet,crossingVelocity,
      crossingZ,crossingQ,crossingQx];ring)

theorem crossing_transport (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    crossingMaterialDerivative β μ m (backwardB β μ) s x = 0 ∧
    crossingMaterialDerivative β μ m (backwardC β μ) s x =
      backwardC β μ (s,x) * backwardQ β μ m (s,x) ∧
    crossingMaterialDerivative β μ m (backwardZ β μ) s x =
      backwardZ β μ (s,x) * backwardQ β μ m (s,x) -
        deriv (fun y => backwardQ β μ m (s,y)) x / 2 ∧
    crossingMaterialDerivative β μ m (actualCrossingPhi β μ m) s x =
      backwardQ β μ m (s,x) * actualCrossingPhi β μ m (s,x) +
        backwardZ β μ (s,x) * backwardHx β μ m (s,x) ∧
    crossingMaterialDerivative β μ m (fun p => Real.log (parisiForwardDensity β μ p.1 p.2)) s x =
      bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x / 2 -
        backwardZ β μ (s,x) ^ 2 - m * backwardC β μ (s,x) ∧
    deriv (fun r => crossingPhysicalWeight β μ r x) s / β ^ 2 +
      deriv (fun y => actualCrossingVelocity β μ m (s,y) * crossingPhysicalWeight β μ s y) x =
      (bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x / 2 -
        backwardQ β μ m (s,x) - backwardH β μ m (s,x)) * crossingPhysicalWeight β μ s x ∧
    -deriv (fun y => crossingPhysicalWeight β μ s y * backwardZ β μ (s,y)) x /
        crossingPhysicalWeight β μ s x =
      actualCrossingPhi β μ m (s,x) + bridgeCrossingPsi β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x := by
  have ht : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
  have hm : parisiCDF μ s = m := hc s ⟨hs.1.le,hs.2⟩
  have hv : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ
  refine ⟨?_,?_,actualCrossing_transport_z β hβ μ ha hab hb hc hs x,?_,?_,?_,?_⟩
  · unfold crossingMaterialDerivative
    have hxB := hasDerivAt_backwardD β μ 1 s x ⟨ht.1.le,ht.2⟩
    change HasDerivAt (fun y => backwardB β μ (s,y)) (backwardC β μ (s,x)) x at hxB
    rw [hxB.deriv]
    have hh := actualCrossing_transport_B β hβ μ ha hab hb hc hs x
    apply divide_transport _ _ _ _ hv
    convert hh using 1 <;> ring
  · unfold crossingMaterialDerivative
    have hxC := hasDerivAt_backwardD β μ 2 s x ⟨ht.1.le,ht.2⟩
    change HasDerivAt (fun y => backwardC β μ (s,y)) (backwardD β μ 3 (s,x)) x at hxC
    rw [hxC.deriv]
    have hh := actualCrossing_transport_C β hβ μ ha hab hb hc hs x
    apply divide_transport _ _ _ _ hv
    convert hh using 1 <;> ring
  · unfold crossingMaterialDerivative
    rw [(hasDerivAt_actualCrossingPhi_constantCDF_time β hβ μ ha hab hb hc hs x).deriv,
      (hasDerivAt_actualCrossingPhi β hβ μ m s x ⟨ht.1.le,ht.2⟩).deriv,
      mul_div_cancel_left₀ _ hv]
    ring
  · unfold crossingMaterialDerivative
    have hh := actual_crossing_log_density_transport β hβ μ ha hab hb hc hs x
    apply divide_transport _ _ _ _ hv
    convert! hh using 1 <;> ring
  · have hh := actual_crossing_weight_transport β hβ μ ha hab hb hc hs x
    apply divide_transport _ _ _ _ hv
    convert! hh using 1 <;> ring
  · rw [crossingPhysicalWeight_eq β μ ht,
      (hasDerivAt_bridgeCrossingWeight_mul_z β hβ μ s ht x).deriv,hm]
    field_simp [(bridgeCrossingWeight_pos β hβ μ s ht x).ne']

end FRSB
