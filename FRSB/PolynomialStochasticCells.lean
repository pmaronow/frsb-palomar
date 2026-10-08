module

public import FRSB.PolynomialMomentCells
public import FRSB.ItoStochasticTools
public import Paper.ParisiStateShift

@[expose] public section

/-! Literal stochastic polynomial identities on actual finite Parisi cells.
The stochastic term is realized by Brownian adapted left sums on the actual
cropped interval, rather than assumed as a structure field. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper MvPolynomial
open scoped Topology NNReal BigOperators
namespace FRSB
set_option maxHeartbeats 1000000
open SpinGlass.Targets

 theorem polynomialStochasticLeftSums_finite_cell (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) (F : MomentPolynomial) (l r : ℝ≥0)
    (hl : s.q p < (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) < s.q (p+1)) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t ω => polynomialJetField β (parisiSchemeMeasure s)
          (polynomialSpatialDerivative F) ((l : ℝ)+t)
          (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) (l+t) ω))
        (r-l) (n+1) (r-l)) atTop
      (fun ω => polynomialJetField β (parisiSchemeMeasure s) F r
          (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) r ω)-
        polynomialJetField β (parisiSchemeMeasure s) F l
          (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) l ω)-
        ∫t in (l : ℝ)..(r : ℝ),β^2*(
          polynomialJetField β (parisiSchemeMeasure s) (momentDrift0 F) t
            (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)+
          parisiCDF (parisiSchemeMeasure s) t*
            polynomialJetField β (parisiSchemeMeasure s) (momentDrift1 F) t
              (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω))) := by
  let ν := parisiSchemeMeasure s
  let u := polynomialJetField β ν F
  let ut := fun t x => β^2*polynomialJetField β ν (polynomialTimeDerivative (s.m p) F) t x
  let ux := polynomialJetField β ν (polynomialSpatialDerivative F)
  let uxx := polynomialJetField β ν (polynomialSpatialDerivative (polynomialSpatialDerivative F))
  let f := interiorCappedTest u (s.q p) l r (s.q (p+1))
  let fR := timeShiftTest f l
  let X := fun t ω => selectedParisiItoState β 0 hβ ν (l+t) ω
  let d := fun t ω => selectedParisiItoDrift β 0 hβ ν (l+t) ω
  let T := r-l
  have hc : BoundedDriftItoCharacteristics canonicalBrownianMeasure
      (canonicalBrownianShiftFiltration l) X d (canonicalDiracShiftMartingale β l) β :=
    boundedDriftItoCharacteristics_canonicalParisiShift β 0 ν
      (fun t x => parisiGradient β ν (t,x)) (continuous_parisiGradient β ν)
      (fun t x => norm_parisiGradient_le_one β ν (t,x))
      (lipschitzWith_parisiGradient β hβ ν) l
  have hut : ∀ t ∈ Ioo (s.q p) (s.q (p+1)), ∀ x,
      HasDerivAt (fun t => u t x) (ut t x) t :=
    fun t ht x => hasDerivAt_finiteCell_polynomialJetField_time β hβ s hp hq F ht x
  have hux : ∀ t x, HasDerivAt (u t) (ux t x) x :=
    fun t x => hasDerivAt_polynomialJetField_spatial β ν F t x
  have huxx : ∀ t x, HasDerivAt (ux t) (uxx t x) x :=
    fun t x => hasDerivAt_polynomialJetField_spatial β ν _ t x
  obtain ⟨hfc,hft,hfs,hfdt,hfx,hfxx⟩ := interiorCappedTest_regular u ut ux uxx
    (s.q p) l r (s.q (p+1)) hl (NNReal.coe_le_coe.mpr hlr) hr
    (continuous_polynomialJetField β ν F)
    (continuous_const.mul (continuous_polynomialJetField β ν _))
    (continuous_polynomialJetField β ν _) (continuous_polynomialJetField β ν _)
    hut hux huxx (fun t => (contDiff_polynomialJetField_spatial β ν F t).of_le (by simp))
  obtain ⟨hRc,hRt,hRs,hRdt,hRx,hRxx⟩ := timeShiftTest_regular f l hfc hft hfs hfdt hfx hfxx
  have hwindow {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T : ℝ)) :
      (l : ℝ)+t ∈ Icc (l : ℝ) (r : ℝ) := by
    have hT : (T : ℝ)=(r : ℝ)-l := NNReal.coe_sub hlr
    constructor <;> linarith [ht.1,ht.2]
  have htime {t : ℝ} (ht : 0 ≤ t) : l+t.toNNReal=((l : ℝ)+t).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht,
      Real.coe_toNNReal _ (add_nonneg l.coe_nonneg ht)]
  let source : ℝ → BrownianSample → ℝ := fun t ω => β^2*(
    polynomialJetField β ν (momentDrift0 F) ((l : ℝ)+t) (X t.toNNReal ω)+
      parisiCDF ν ((l : ℝ)+t)*
        polynomialJetField β ν (momentDrift1 F) ((l : ℝ)+t) (X t.toNNReal ω))
  have hgen : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T : ℝ),
      hjbGenerator X d β fR t ω=source t ω := by
    intro ω t ht
    have htw := hwindow ht
    have htl0 : 0 ≤ (l : ℝ)+t := add_nonneg l.coe_nonneg ht.1
    have htl1 : (l : ℝ)+t ≤ 1 := htw.2.trans (hr.le.trans (s.q_le_one (by omega)))
    have hCDF : parisiCDF ν ((l : ℝ)+t)=s.m p :=
      parisiCDF_scheme_cell s hp ⟨hl.le.trans htw.1,htw.2.trans_lt hr⟩
    have hdr : d t.toNNReal ω=β^2*parisiCDF ν ((l : ℝ)+t)*
        parisiGradient β ν (((l : ℝ)+t),X t.toNNReal ω) := by
      simp only [d,selectedParisiItoDrift,canonicalParisiItoDrift,NNReal.coe_add,
        Real.coe_toNNReal _ ht.1,ite_eq_left htl1,X,selectedParisiItoState]
    unfold hjbGenerator
    rw [timeShiftTest_timeDerivative f l t _ hft,
      timeShiftTest_spaceDerivative,timeShiftTest_spaceSecondDerivative,
      interiorCappedTest_timeDerivative u ut (s.q p) l r (s.q (p+1)) hl
        (NNReal.coe_le_coe.mpr hlr) hr hut,
      interiorCappedTest_spaceDerivative u ux hux,
      interiorCappedTest_spaceSecondDerivative u ux uxx hux huxx,
      interiorTimeCap_eq _ _ _ _ _ htw,interiorTimeCapD_eq _ _ _ _ _ htw,mul_one,hdr]
    dsimp only [source,ut,ux,uxx]
    rw [hCDF,←parisiSpatialJet_one]
    exact polynomialJetField_generator_identity β ν (s.m p) F ((l : ℝ)+t) (X t.toNNReal ω)
  have hconv := ito_stochastic_leftSums_source hc fR hRc hRt hRs hRdt hRx hRxx T source hgen
  have hleft (n : ℕ) (ω : BrownianSample) :
      uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t ω => itoSpaceDerivative fR t (X t ω)) T (n+1) T ω =
      uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t ω => polynomialJetField β ν (polynomialSpatialDerivative F) ((l : ℝ)+t)
          (selectedParisiItoState β 0 hβ ν (l+t) ω)) T (n+1) T ω := by
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal,
      uniformAdaptedMartingaleLeftSumProcess_terminal]
    apply Finset.sum_congr rfl
    intro i hi
    have hiT : (uniformPartitionTime T (n+1) i : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
      uniformPartitionTime_mem_Icc_of_le T (Nat.succ_pos n)
        (Nat.le_of_lt (Finset.mem_range.mp hi))
    have htw := hwindow hiT
    rw [timeShiftTest_spaceDerivative,
      interiorCappedTest_spaceDerivative u ux hux]
    congr 1
    change ux (interiorTimeCap (s.q p) l r (s.q (p+1)) _) _ = ux _ _
    congr 1
    exact interiorTimeCap_eq (s.q p) l r (s.q (p+1)) _ htw
  have heval (t : ℝ≥0) (ht : t ∈ Icc 0 T) (ω : BrownianSample) :
      fR t (X t ω)=polynomialJetField β ν F ((l : ℝ)+t)
        (selectedParisiItoState β 0 hβ ν (l+t) ω) := by
    dsimp only [fR,timeShiftTest,f,interiorCappedTest]
    have htR : (t : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) := ⟨by exact_mod_cast ht.1,by exact_mod_cast ht.2⟩
    congr 1
    exact interiorTimeCap_eq (s.q p) l r (s.q (p+1)) _ (hwindow htR)
  have hint (ω : BrownianSample) : (∫t in (0 : ℝ)..(T : ℝ),source t ω)=
      ∫t in (l : ℝ)..(r : ℝ),β^2*(
        polynomialJetField β ν (momentDrift0 F) t
          (selectedParisiItoState β 0 hβ ν t.toNNReal ω)+
        parisiCDF ν t*polynomialJetField β ν (momentDrift1 F) t
          (selectedParisiItoState β 0 hβ ν t.toNNReal ω)) := by
    let g := fun t => β^2*(polynomialJetField β ν (momentDrift0 F) t
      (selectedParisiItoState β 0 hβ ν t.toNNReal ω)+parisiCDF ν t*
        polynomialJetField β ν (momentDrift1 F) t
          (selectedParisiItoState β 0 hβ ν t.toNNReal ω))
    have he : (∫t in (0 : ℝ)..(T : ℝ),source t ω)=∫t in (0 : ℝ)..(T : ℝ),g ((l : ℝ)+t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le T.coe_nonneg
      intro t ht
      dsimp only [source,g,X]
      rw [htime ht.1.le]
    rw [he,intervalIntegral.integral_comp_add_left]
    simp only [add_zero,show (l : ℝ)+(T : ℝ)=(r : ℝ) by rw [NNReal.coe_sub hlr];ring]
    rfl
  have hconv' := hconv.congr_left (fun n => .of_forall (hleft n))
  apply TendstoInMeasure.congr_right _ hconv'
  exact .of_forall fun ω => by
    dsimp only
    have hTe := heval T ⟨by positivity,le_rfl⟩ ω
    have h0e := heval 0 ⟨le_rfl,by positivity⟩ ω
    have hTr : (l : ℝ)+(T : ℝ)=(r : ℝ) := by rw [NNReal.coe_sub hlr];ring
    have hTN : l+T=r := add_tsub_cancel_of_le hlr
    rw [hTr,hTN] at hTe
    simp only [NNReal.coe_zero,add_zero] at h0e
    rw [hTe,h0e,hint ω]

end FRSB
