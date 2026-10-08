module

public import FRSB.CrossingActualTime
public import FRSB.CrossingBridgeDifferentiation
public import FRSB.ForwardDensityRegularity

@[expose] public section

/-! The literal actual density and weighted-density transport equations.
Time derivatives use physical overlap time; beta squared converts them to
Section 5's clock. No forward PDE or temporal regularity is assumed. -/
noncomputable section
open Set Paper
namespace FRSB
set_option maxHeartbeats 1500000

def crossingPhysicalWeight (β : ℝ) (μ : ParisiMeasure) (s x : ℝ) : ℝ :=
  2 * backwardC β μ (s,x) ^ 2 * parisiForwardDensity β μ s x

def crossingPhysicalWeightT (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) : ℝ :=
  4 * backwardC β μ (s,x) * (β ^ 2 * crossingCt m (backwardB β μ (s,x))
    (backwardC β μ (s,x)) (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x))) *
      parisiForwardDensity β μ s x +
  2 * backwardC β μ (s,x) ^ 2 * parisiForwardDensityT β μ m s x

theorem crossingPhysicalWeight_eq (β : ℝ) (μ : ParisiMeasure) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    crossingPhysicalWeight β μ s = bridgeCrossingWeight β μ s hs := by
  funext x
  simp only [crossingPhysicalWeight,bridgeCrossingWeight,parisiForwardDensity_eq β μ hs]

theorem iteratedDeriv_forwardBridgeDensity_two_score (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 2 (forwardBridgeDensity β μ s hs) x =
      (parisiCDF μ s * backwardC β μ (s,x) - bridgeCrossingVxx β μ s hs x +
        (parisiCDF μ s * backwardB β μ (s,x) - bridgeCrossingVx β μ s hs x) ^ 2) *
          forwardBridgeDensity β μ s hs x := by
  have he : deriv (forwardBridgeDensity β μ s hs) = fun y =>
      (parisiCDF μ s * backwardB β μ (s,y) - bridgeCrossingVx β μ s hs y) *
        forwardBridgeDensity β μ s hs y :=
    funext (fun y => (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs y).deriv)
  rw [show (2 : ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,he]
  have hd := (((hasDerivAt_backwardD β μ 1 s x ⟨hs.1.le,hs.2⟩).const_mul
    (parisiCDF μ s)).sub (hasDerivAt_bridgeCrossingVx β μ s hs x)).mul
      (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x)
  convert hd.deriv using 1
  · rfl
  · dsimp only [Pi.sub_apply,Pi.mul_apply,backwardB,backwardC]
    ring

theorem hasDerivAt_crossingPhysicalWeight_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => crossingPhysicalWeight β μ r x)
      (crossingPhysicalWeightT β μ m s x) s := by
  have hd := (((hasDerivAt_backwardC_constantCDF_time β hβ μ ha hab hb hc hs x).pow 2).const_mul 2).mul
    (hasDerivAt_parisiForwardDensity_T β hβ μ ha hab hb hc hs x)
  convert hd using 1
  · rfl
  · dsimp only [crossingPhysicalWeightT,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,pow_one]
    ring

theorem crossingPhysicalWeightT_eq_transport (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    crossingPhysicalWeightT β μ (parisiCDF μ s) s x = β ^ 2 *
      (actualCrossingVelocity β μ (parisiCDF μ s) (s,x) *
        (bridgeCrossingN β μ s hs x + 3 * backwardZ β μ (s,x)) +
          bridgeCrossingK β μ s hs x / 2 - backwardH β μ (parisiCDF μ s) (s,x)) *
            bridgeCrossingWeight β μ s hs x := by
  have hC := (backwardC_pos β hβ μ s x ⟨hs.1.le,hs.2⟩).ne'
  unfold crossingPhysicalWeightT parisiForwardDensityT
  rw [parisiForwardDensity_eq β μ hs,iteratedDeriv_forwardBridgeDensity_two_score β hβ μ s hs x,
    (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x).deriv]
  simp_rw [← backwardD_eq_spatialJet]
  dsimp [actualCrossingVelocity,crossingVelocity,bridgeCrossingK,crossingK,
    bridgeCrossingN,crossingCt,bridgeCrossingWeight,backwardH,backwardHJet,backwardQJet,
    backwardZxJet,backwardZ,backwardZJet,backwardC,backwardB] at *
  field_simp
  ring

/-- The genuine conservation law for the actual weight. -/
theorem actual_crossing_weight_transport (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => crossingPhysicalWeight β μ r x) s + β ^ 2 *
      deriv (fun y => actualCrossingVelocity β μ m (s,y) * crossingPhysicalWeight β μ s y) x =
        β ^ 2 * (bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x / 2 -
          backwardQ β μ m (s,x) - backwardH β μ m (s,x)) * crossingPhysicalWeight β μ s x := by
  let ht : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
  have hm : parisiCDF μ s = m := hc s ⟨hs.1.le,hs.2⟩
  have hv : HasDerivAt (fun y => actualCrossingVelocity β μ m (s,y))
      (-backwardQ β μ m (s,x)) x := by
    have hd := ((hasDerivAt_backwardD β μ 1 s x ⟨ht.1.le,ht.2⟩).const_mul m).sub
      (hasDerivAt_backwardZ β hβ μ s x ⟨ht.1.le,ht.2⟩)
    convert hd using 1
    · rfl
    · dsimp [backwardQ,backwardQJet,backwardZx,backwardC]
      ring
  have hder := (hv.mul (hasDerivAt_bridgeCrossingWeight β hβ μ s ht x)).deriv
  change deriv (fun y => actualCrossingVelocity β μ m (s,y) * bridgeCrossingWeight β μ s ht y) x = _ at hder
  rw [(hasDerivAt_crossingPhysicalWeight_time β hβ μ ha hab hb hc hs x).deriv,
    crossingPhysicalWeight_eq β μ ht,hder,← hm,crossingPhysicalWeightT_eq_transport β hβ μ s ht x]
  ring

/-- The actual density's time source in the crossing variables. -/
theorem parisiForwardDensityT_eq_crossing_score (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    parisiForwardDensityT β μ (parisiCDF μ s) s x = β ^ 2 *
      (bridgeCrossingK β μ s hs x / 2 - backwardZ β μ (s,x) ^ 2 -
        parisiCDF μ s * backwardC β μ (s,x) -
        actualCrossingVelocity β μ (parisiCDF μ s) (s,x) *
          (backwardZ β μ (s,x) - bridgeCrossingN β μ s hs x)) *
            forwardBridgeDensity β μ s hs x := by
  unfold parisiForwardDensityT
  rw [parisiForwardDensity_eq β μ hs,iteratedDeriv_forwardBridgeDensity_two_score β hβ μ s hs x,
    (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x).deriv]
  simp_rw [← backwardD_eq_spatialJet]
  dsimp [actualCrossingVelocity,crossingVelocity,bridgeCrossingK,crossingK,
    bridgeCrossingN,backwardC,backwardB]
  ring

theorem hasDerivAt_log_parisiForwardDensity_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (fun y => Real.log (parisiForwardDensity β μ s y))
      (backwardZ β μ (s,x) - bridgeCrossingN β μ s hs x) x := by
  rw [parisiForwardDensity_eq β μ hs]
  have hp := (forwardBridgeDensity_pos β hβ μ s hs x).ne'
  convert (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x).log hp using 1
  dsimp [bridgeCrossingN]
  field_simp
  ring

/-- Literal log-density transport with the paper's clock conversion. -/
theorem actual_crossing_log_density_transport (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => Real.log (parisiForwardDensity β μ r x)) s + β ^ 2 *
      actualCrossingVelocity β μ m (s,x) * deriv (fun y => Real.log (parisiForwardDensity β μ s y)) x =
        β ^ 2 * (bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x / 2 -
          backwardZ β μ (s,x) ^ 2 - m * backwardC β μ (s,x)) := by
  let ht : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩
  have hm : parisiCDF μ s = m := hc s ⟨hs.1.le,hs.2⟩
  have hp : parisiForwardDensity β μ s x ≠ 0 := by
    rw [parisiForwardDensity_eq β μ ht]
    exact (forwardBridgeDensity_pos β hβ μ s ht x).ne'
  rw [((hasDerivAt_parisiForwardDensity_T β hβ μ ha hab hb hc hs x).log hp).deriv,
    (hasDerivAt_log_parisiForwardDensity_spatial β hβ μ s ht x).deriv,← hm,
    parisiForwardDensityT_eq_crossing_score β hβ μ s ht x,parisiForwardDensity_eq β μ ht]
  field_simp [(forwardBridgeDensity_pos β hβ μ s ht x).ne']
  ring

end FRSB
