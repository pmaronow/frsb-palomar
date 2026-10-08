module

public import FRSB.CrossMagnetizationTime

@[expose] public section

/-! The literal magnetization-coordinate conclusions of Remark 5.3.
The final identities use the paper's forward clock t=beta^2*s. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB

 theorem magnetizationInverse_odd (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    magnetizationInverse β μ s (-v) = -magnetizationInverse β μ s v := by
  apply (parisiGradient_strictMono β hβ μ s hs).injective
  dsimp only
  rw [parisiGradient_magnetizationInverse β hβ μ s (-v) hs
      (show -v ∈ Ioo (-1 : ℝ) 1 from ⟨by linarith [hv.2],by linarith [hv.1]⟩),
    parisiGradient_odd β hβ μ s _ hs,parisiGradient_magnetizationInverse β hβ μ s v hs hv]

 theorem magnetizationDensity_even (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    magnetizationDensity β μ s hs (-v) = magnetizationDensity β μ s hs v := by
  unfold magnetizationDensity
  rw [magnetizationInverse_odd β hβ μ s ⟨hs.1.le,hs.2⟩ hv,
    forwardBridgeDensity_even]
  unfold backwardC
  rw [backwardD_reflect β μ s ⟨hs.1.le,hs.2⟩ 2]
  norm_num

 theorem magnetizationR_even (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    magnetizationR β μ s (-v) = magnetizationR β μ s v := by
  simp only [magnetizationR,parisiForwardDensity_eq β μ hs]
  rw [magnetizationInverse_odd β hβ μ s ⟨hs.1.le,hs.2⟩ hv,
    forwardBridgeDensity_even]
  unfold backwardC
  rw [backwardD_reflect β μ s ⟨hs.1.le,hs.2⟩ 2]
  norm_num

 theorem contDiffAt_magnetizationR_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) : ContDiffAt ℝ ∞ (magnetizationR β μ s) v := by
  have hi := contDiffAt_magnetizationInverse β hβ μ s v ⟨hs.1.le,hs.2⟩ hv
  have hp := (contDiff_forwardBridgeDensity β μ s hs).contDiffAt.comp v hi
  have hC := (contDiff_backwardD_spatial β μ s ⟨hs.1.le,hs.2⟩ 2).contDiffAt.comp v hi
  convert hp.mul hC using 1
  funext b
  simp only [magnetizationR,parisiForwardDensity_eq β μ hs,Function.comp_def,backwardC]

/-- K is exactly the sum of the two spatial logarithmic-derivative
expressions asserted in the remark. -/
 theorem bridgeCrossingK_spatial_identity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    bridgeCrossingK β μ s hs x =
      (bridgeCrossingN β μ s hs x^2-deriv (bridgeCrossingN β μ s hs) x)+
      (backwardZ β μ (s,x)^2+deriv (fun y => backwardZ β μ (s,y)) x) := by
  rw [(hasDerivAt_bridgeCrossingN β hβ μ s hs x).deriv,
    (hasDerivAt_backwardZ β hβ μ s x ⟨hs.1.le,hs.2⟩).deriv]
  dsimp only [bridgeCrossingK,crossingK,backwardQ,backwardQJet,backwardZx]
  ring

 def forwardMagnetizationInverse (β : ℝ) (μ : ParisiMeasure) (t v : ℝ) : ℝ :=
  magnetizationInverse β μ (t/β^2) v

 def forwardMagnetizationChi (β : ℝ) (μ : ParisiMeasure) (t v : ℝ) : ℝ :=
  backwardC β μ (t/β^2,forwardMagnetizationInverse β μ t v)

 def forwardMagnetizationR (β : ℝ) (μ : ParisiMeasure) (t v : ℝ) : ℝ :=
  magnetizationR β μ (t/β^2) v

 theorem hasDerivAt_forwardMagnetizationInverse_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => forwardMagnetizationInverse β μ r v)
      (actualCrossingVelocity β μ m (t/β^2,forwardMagnetizationInverse β μ t v)) t := by
  have hd := (hasDerivAt_magnetizationInverse_time β hβ μ ha hab hb hc ht hv).comp t
    ((hasDerivAt_id t).div_const (β^2))
  convert hd using 1
  · rfl
  · dsimp only [forwardMagnetizationInverse]
    field_simp

 theorem forwardMagnetizationR_weighted_law (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun r => forwardMagnetizationR β μ r v) t =
      forwardMagnetizationChi β μ t v^2 * deriv (deriv (forwardMagnetizationR β μ t)) v/2+
        2*backwardQ β μ m (t/β^2,forwardMagnetizationInverse β μ t v)*
          forwardMagnetizationR β μ t v := by
  have hd := (hasDerivAt_magnetizationR_time β hβ μ ha hab hb hc ht hv).comp t
    ((hasDerivAt_id t).div_const (β^2))
  have hh := magnetizationR_weighted_law β hβ μ ha hab hb hc ht hv
  rw [(hasDerivAt_magnetizationR_time β hβ μ ha hab hb hc ht hv).deriv] at hh
  have hfn : (fun r => forwardMagnetizationR β μ r v) =
      (fun s => magnetizationR β μ s v) ∘ (fun r => r/β^2) := rfl
  simp only [id_eq] at hd
  rw [hfn,hd.deriv]
  have hn : β^2 ≠ 0 := pow_ne_zero 2 hβ
  have hsp : forwardMagnetizationR β μ t = magnetizationR β μ (t/β^2) := rfl
  rw [hsp]
  dsimp only [forwardMagnetizationChi,forwardMagnetizationInverse,forwardMagnetizationR]
  rw [hh]
  field_simp

 theorem forwardMagnetizationR_log_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun r => Real.log (forwardMagnetizationR β μ r v)) t =
      bridgeCrossingK β μ (t/β^2) ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩
        (forwardMagnetizationInverse β μ t v)/2-
        backwardQ β μ m (t/β^2,forwardMagnetizationInverse β μ t v)-
        backwardH β μ m (t/β^2,forwardMagnetizationInverse β μ t v) := by
  let hs : t/β^2 ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩
  have hp := (magnetizationR_pos β hβ μ (t/β^2) hs v).ne'
  have hd := ((hasDerivAt_magnetizationR_time β hβ μ ha hab hb hc ht hv).log hp).comp t
    ((hasDerivAt_id t).div_const (β^2))
  have hfn : (fun r => Real.log (forwardMagnetizationR β μ r v)) =
      (fun s => Real.log (magnetizationR β μ s v)) ∘ (fun r => r/β^2) := rfl
  simp only [id_eq] at hd
  rw [hfn,hd.deriv]
  dsimp only [forwardMagnetizationInverse]
  field_simp

 theorem forwardMagnetizationR_log_score (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t/β^2 ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    bridgeCrossingN β μ (t/β^2) ht (forwardMagnetizationInverse β μ t v)+
      backwardZ β μ (t/β^2,forwardMagnetizationInverse β μ t v) =
        -forwardMagnetizationChi β μ t v *
          deriv (fun b => Real.log (forwardMagnetizationR β μ t b)) v :=
  magnetizationR_log_score β hβ μ (t/β^2) ht hv

 theorem forwardMagnetizationR_centered_identity (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t/β^2 ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    -deriv (fun b => forwardMagnetizationChi β μ t b*
      backwardZ β μ (t/β^2,forwardMagnetizationInverse β μ t b)*forwardMagnetizationR β μ t b) v /
        forwardMagnetizationR β μ t v =
      actualCrossingPhi β μ (parisiCDF μ (t/β^2)) (t/β^2,forwardMagnetizationInverse β μ t v)+
        bridgeCrossingPsi β μ (t/β^2) ht (forwardMagnetizationInverse β μ t v) :=
  magnetizationR_centered_identity β hβ μ (t/β^2) ht hv

 theorem forwardMagnetizationChi_log_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun r => Real.log (forwardMagnetizationChi β μ r v)) t =
      backwardQ β μ m (t/β^2,forwardMagnetizationInverse β μ t v) := by
  have hp := (backwardC_pos β hβ μ (t/β^2) (magnetizationInverse β μ (t/β^2) v)
    ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩).ne'
  have hd := ((hasDerivAt_magnetizationCurvature_time β hβ μ ha hab hb hc ht hv).log hp).comp t
    ((hasDerivAt_id t).div_const (β^2))
  have hfn : (fun r => Real.log (forwardMagnetizationChi β μ r v)) =
      (fun s => Real.log (backwardC β μ (s,magnetizationInverse β μ s v))) ∘
        (fun r => r/β^2) := rfl
  simp only [id_eq] at hd
  rw [hfn,hd.deriv]
  dsimp only [forwardMagnetizationInverse]
  field_simp

 theorem magnetizationR_second_spatial_expanded (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    backwardC β μ (s,magnetizationInverse β μ s v)^2 *
      deriv (deriv (magnetizationR β μ s)) v / (2*magnetizationR β μ s v) =
        (bridgeCrossingN β μ s hs (magnetizationInverse β μ s v)^2-
          backwardZ β μ (s,magnetizationInverse β μ s v)^2-
          deriv (bridgeCrossingN β μ s hs) (magnetizationInverse β μ s v)-
          deriv (fun x => backwardZ β μ (s,x)) (magnetizationInverse β μ s v))/2 := by
  rw [(hasDerivAt_deriv_magnetizationR_spatial β hβ μ s hs hv).deriv,
    (hasDerivAt_bridgeCrossingN β hβ μ s hs (magnetizationInverse β μ s v)).deriv,
    (hasDerivAt_backwardZ β hβ μ s (magnetizationInverse β μ s v) ⟨hs.1.le,hs.2⟩).deriv,
    magnetizationR_eq_weightedDensity β μ s hs]
  have hp := (forwardBridgeDensity_pos β hβ μ s hs (magnetizationInverse β μ s v)).ne'
  have hC := (backwardC_pos β hβ μ s (magnetizationInverse β μ s v) ⟨hs.1.le,hs.2⟩).ne'
  dsimp only [magnetizationWeightedDensity]
  field_simp
  ring

 theorem forwardMagnetizationR_second_spatial_rates (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t/β^2 ∈ Ioc (0 : ℝ) 1) {v : ℝ}
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    let s := t/β^2
    let x := forwardMagnetizationInverse β μ t v
    forwardMagnetizationChi β μ t v^2*deriv (deriv (forwardMagnetizationR β μ t)) v /
      (2*forwardMagnetizationR β μ t v) =
        (bridgeCrossingN β μ s ht x^2-backwardZ β μ (s,x)^2-
          deriv (bridgeCrossingN β μ s ht) x-deriv (fun y => backwardZ β μ (s,y)) x)/2 ∧
    forwardMagnetizationChi β μ t v^2*deriv (deriv (forwardMagnetizationR β μ t)) v /
      (2*forwardMagnetizationR β μ t v) =
        bridgeCrossingK β μ s ht x/2-3*backwardQ β μ (parisiCDF μ s) (s,x)-
          backwardH β μ (parisiCDF μ s) (s,x) :=
  ⟨magnetizationR_second_spatial_expanded β hβ μ (t/β^2) ht hv,
    magnetizationR_second_spatial_rate β hβ μ (t/β^2) ht hv⟩

/-- All coordinate and density identities in Remark 5.3, in one closed
statement for the actual PDE, optimal state, and normalized crossing law. -/
 theorem magnetization_weighted_law_remark (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    let s := t/β^2
    let hs : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩
    let x := forwardMagnetizationInverse β μ t v
    canonicalBrownianMeasure.map (M β μ s) =
      (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
        (fun b => ENNReal.ofReal (magnetizationDensity β μ s hs b)) ∧
    (crossingWeightLaw (bridgeCrossingWeight β μ s hs)).map
      (fun x => parisiGradient β μ (s,x)) =
      (volume.restrict (Ico (0 : ℝ) 1)).withDensity
        (fun b => ENNReal.ofReal (2*magnetizationWeightedDensity β μ s hs b /
          curvatureMoment2 β μ s)) ∧
    magnetizationWeightedDensity β μ s hs v =
      forwardMagnetizationChi β μ t v^2 * magnetizationDensity β μ s hs v ∧
    deriv (fun r => forwardMagnetizationInverse β μ r v) t = actualCrossingVelocity β μ m (s,x) ∧
    deriv (fun r => forwardMagnetizationR β μ r v) t =
      forwardMagnetizationChi β μ t v^2 * deriv (deriv (forwardMagnetizationR β μ t)) v/2+
        2*backwardQ β μ m (s,x)*forwardMagnetizationR β μ t v ∧
    deriv (fun r => Real.log (forwardMagnetizationR β μ r v)) t =
      bridgeCrossingK β μ s hs x/2-backwardQ β μ m (s,x)-backwardH β μ m (s,x) ∧
    bridgeCrossingN β μ s hs x+backwardZ β μ (s,x) =
      -forwardMagnetizationChi β μ t v*deriv (fun b => Real.log (forwardMagnetizationR β μ t b)) v ∧
    bridgeCrossingK β μ s hs x =
      (bridgeCrossingN β μ s hs x^2-deriv (bridgeCrossingN β μ s hs) x)+
        (backwardZ β μ (s,x)^2+deriv (fun y => backwardZ β μ (s,y)) x) ∧
    deriv (fun r => Real.log (forwardMagnetizationChi β μ r v)) t = backwardQ β μ m (s,x) ∧
    (forwardMagnetizationChi β μ t v^2*deriv (deriv (forwardMagnetizationR β μ t)) v /
      (2*forwardMagnetizationR β μ t v) =
        (bridgeCrossingN β μ s hs x^2-backwardZ β μ (s,x)^2-
          deriv (bridgeCrossingN β μ s hs) x-deriv (fun y => backwardZ β μ (s,y)) x)/2 ∧
      forwardMagnetizationChi β μ t v^2*deriv (deriv (forwardMagnetizationR β μ t)) v /
        (2*forwardMagnetizationR β μ t v) =
          bridgeCrossingK β μ s hs x/2-3*backwardQ β μ (parisiCDF μ s) (s,x)-
            backwardH β μ (parisiCDF μ s) (s,x)) ∧
    -deriv (fun b => forwardMagnetizationChi β μ t b*
      backwardZ β μ (s,forwardMagnetizationInverse β μ t b)*forwardMagnetizationR β μ t b) v /
        forwardMagnetizationR β μ t v =
      actualCrossingPhi β μ (parisiCDF μ s) (s,x)+bridgeCrossingPsi β μ s hs x := by
  dsimp only
  exact ⟨magnetizationState_density_law β hβ μ _ _,
    crossingWeightLaw_magnetization_density β hβ μ _ _,
    magnetizationWeightedDensity_eq_chi_sq_density β hβ μ _ _ v,
    (hasDerivAt_forwardMagnetizationInverse_time β hβ μ ha hab hb hc ht hv).deriv,
    forwardMagnetizationR_weighted_law β hβ μ ha hab hb hc ht hv,
    forwardMagnetizationR_log_time β hβ μ ha hab hb hc ht hv,
    forwardMagnetizationR_log_score β hβ μ t _ hv,
    bridgeCrossingK_spatial_identity β hβ μ _ _ _,
    forwardMagnetizationChi_log_time β hβ μ ha hab hb hc ht hv,
    forwardMagnetizationR_second_spatial_rates β hβ μ t _ hv,
    forwardMagnetizationR_centered_identity β hβ μ t _ hv⟩

end FRSB
