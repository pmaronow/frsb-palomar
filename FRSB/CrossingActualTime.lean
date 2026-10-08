module

public import FRSB.CrossingActualFields
public import FRSB.CrossingJet
public import FRSB.BackwardsConstantTime
public import FRSB.JetGenerator

@[expose] public section

/-! Actual constant-mass transport equations in physical time. The factor
beta squared converts the paper's forward clock into physical overlap time. -/
noncomputable section
open Set Paper
namespace FRSB
set_option maxHeartbeats 1000000

theorem cellTimeForcing_one_crossing (β : ℝ) (μ : ParisiMeasure) (m s x : ℝ) :
    cellTimeForcing β μ m 1 s x = β ^ 2 *
      crossingBt m (backwardB β μ (s,x)) (backwardC β μ (s,x)) (backwardD β μ 3 (s,x)) := by
  rw [cellTimeForcing_eq]
  simp only [Nat.reduceAdd,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,one_mul,Nat.reduceSub]
  simp_rw [← backwardD_eq_spatialJet]
  dsimp [crossingBt,backwardB,backwardC]
  ring

theorem hasDerivAt_backwardB_constantCDF_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardB β μ (r,x))
      (β ^ 2 * crossingBt m (backwardB β μ (s,x)) (backwardC β μ (s,x))
        (backwardD β μ 3 (s,x))) s := by
  have hd := hasDerivAt_constantCDF_spatialJet_time β hβ μ ha hab hb hc 1 hs x
  rw [cellTimeForcing_one_crossing] at hd
  convert hd using 1
  funext r
  exact backwardD_eq_spatialJet β μ 1 r x

theorem hasDerivAt_backwardC_constantCDF_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardC β μ (r,x))
      (β ^ 2 * crossingCt m (backwardB β μ (s,x)) (backwardC β μ (s,x))
        (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x))) s := by
  have hd := hasDerivAt_constantCDF_spatialJet_time β hβ μ ha hab hb hc 2 hs x
  rw [cellTimeForcing_two] at hd
  simp_rw [← backwardD_eq_spatialJet] at hd
  convert hd using 1 <;> first | rfl | (dsimp [crossingCt,backwardB,backwardC]; ring)

theorem hasDerivAt_backwardD_three_constantCDF_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardD β μ 3 (r,x))
      (β ^ 2 * crossingDt m (backwardB β μ (s,x)) (backwardC β μ (s,x))
        (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x)) (backwardD β μ 5 (s,x))) s := by
  have hd := hasDerivAt_constantCDF_spatialJet_time β hβ μ ha hab hb hc 3 hs x
  rw [cellTimeForcing_three] at hd
  simp_rw [← backwardD_eq_spatialJet] at hd
  convert hd using 1
  first | rfl | (dsimp [crossingDt,backwardB,backwardC]; ring)

theorem hasDerivAt_backwardZ_constantCDF_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardZ β μ (r,x))
      (β ^ 2 * crossingZt m (backwardB β μ (s,x)) (backwardC β μ (s,x))
        (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x)) (backwardD β μ 5 (s,x))) s := by
  have hC := (backwardC_pos β hβ μ s x ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩).ne'
  have hd := (hasDerivAt_backwardD_three_constantCDF_time β hβ μ ha hab hb hc hs x).neg.div
    ((hasDerivAt_backwardC_constantCDF_time β hβ μ ha hab hb hc hs x).const_mul 2)
    (mul_ne_zero (by norm_num) hC)
  convert hd using 1
  · funext r; rfl
  · dsimp only [Pi.neg_apply,crossingZt]
    field_simp
    ring

/-- The magnetization is transported without change. -/
theorem actualCrossing_transport_B (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => backwardB β μ (r,x)) s +
      β ^ 2 * actualCrossingVelocity β μ m (s,x) * backwardC β μ (s,x) = 0 := by
  rw [(hasDerivAt_backwardB_constantCDF_time β hβ μ ha hab hb hc hs x).deriv]
  have hC := (backwardC_pos β hβ μ s x ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩).ne'
  have hh := crossing_transport_B_from_jet m (backwardB β μ (s,x)) (backwardC β μ (s,x))
    (backwardD β μ 3 (s,x)) hC
  have he : actualCrossingVelocity β μ m (s,x) =
      crossingVelocity m (backwardB β μ (s,x)) (crossingZ (backwardC β μ (s,x))
        (backwardD β μ 3 (s,x))) := rfl
  rw [he]
  linear_combination β ^ 2 * hh

/-- The transported curvature's logarithmic growth is Q. -/
theorem actualCrossing_transport_C (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => backwardC β μ (r,x)) s +
      β ^ 2 * actualCrossingVelocity β μ m (s,x) * backwardD β μ 3 (s,x) =
        β ^ 2 * backwardC β μ (s,x) * backwardQ β μ m (s,x) := by
  rw [(hasDerivAt_backwardC_constantCDF_time β hβ μ ha hab hb hc hs x).deriv]
  have hC := (backwardC_pos β hβ μ s x ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩).ne'
  have hh := crossing_transport_C_from_jet m (backwardB β μ (s,x)) (backwardC β μ (s,x))
    (backwardD β μ 3 (s,x)) (backwardD β μ 4 (s,x)) hC
  change _ + β ^ 2 * crossingVelocity m _ (crossingZ _ _) * _ =
    β ^ 2 * _ * crossingQ m _ _ _
  linear_combination β ^ 2 * hh

theorem hasDerivAt_actualCrossingPhi_constantCDF_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => actualCrossingPhi β μ m (r,x))
      (β ^ 2 * (backwardQ β μ m (s,x) * actualCrossingPhi β μ m (s,x) +
        backwardZ β μ (s,x) * backwardHx β μ m (s,x) -
        actualCrossingVelocity β μ m (s,x) * (2 * backwardZ β μ (s,x) *
          (2 * backwardQ β μ m (s,x) + 3 * m * backwardC β μ (s,x))))) s := by
  have hd := (((hasDerivAt_backwardZ_constantCDF_time β hβ μ ha hab hb hc hs x).pow 2).const_mul 2).sub
    ((hasDerivAt_backwardC_constantCDF_time β hβ μ ha hab hb hc hs x).const_mul m)
  have hC := (backwardC_pos β hβ μ s x ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩).ne'
  convert hd using 1
  · funext r; rfl
  · dsimp [actualCrossingPhi,crossingPhi,actualCrossingVelocity,backwardZ,backwardZJet,
      backwardQ,backwardQJet,backwardZxJet,backwardHx,backwardHxJet,backwardQxJet,
      backwardZxxJet,crossingZt,crossingCt,crossingDt,backwardC] at *
    field_simp
    ring

end FRSB
