module

public import FRSB.GradientTimeLipschitz
public import FRSB.StoppedOptimalProcess
public import Paper.ItoStateIntegrability

@[expose] public section

/-! A genuine deterministic increment remainder for the actual optimal
magnetization. The time regularity holds through every CDF atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 900000

 theorem spatialGradient_remainder_le (β : ℝ) (μ : ParisiMeasure) (s x y : ℝ) :
    ‖parisiSpatialJet β μ 1 s y-parisiSpatialJet β μ 1 s x-
      parisiSpatialJet β μ 2 s x*(y-x)‖ ≤ uniformSpatialConstant β 2*‖y-x‖^2 := by
  let f : ℝ → ℝ := fun z => parisiSpatialJet β μ 1 s z-parisiSpatialJet β μ 2 s x*(z-x)
  have hd (z : ℝ) : HasDerivAt f
      (parisiSpatialJet β μ 2 s z-parisiSpatialJet β μ 2 s x) z := by
    convert (hasDerivAt_parisiSpatialJet_succ β μ 0 s z).sub
      (((hasDerivAt_id z).sub_const x).const_mul (parisiSpatialJet β μ 2 s x)) using 1
    · rfl
    · simp
  have hdist (z : ℝ) (hz : z ∈ uIcc x y) : ‖z-x‖ ≤ ‖y-x‖ := by
    rw [Real.norm_eq_abs,Real.norm_eq_abs]
    rcases le_total x y with hxy|hyx
    · rw [uIcc_of_le hxy] at hz
      rw [abs_of_nonneg (sub_nonneg.mpr hz.1),abs_of_nonneg (sub_nonneg.mpr hxy)]
      linarith [hz.2]
    · rw [uIcc_of_ge hyx] at hz
      rw [abs_of_nonpos (sub_nonpos.mpr hz.2),abs_of_nonpos (sub_nonpos.mpr hyx)]
      linarith [hz.1]
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hd z).differentiableAt)
    (fun z hz => by
      rw [(hd z).deriv]
      exact (norm_parisiSpatialJet_sub_le β μ 1 s x z).trans
        (mul_le_mul_of_nonneg_left (hdist z hz) (uniformSpatialConstant_pos β 2).le))
    (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
  convert hh using 1 <;> simp only [f,sub_self,mul_zero,sub_zero,pow_two,mul_assoc]
  · congr 1 <;> ring

 theorem norm_integratedDrift_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X d J : ℝ≥0 → Ω → ℝ} {β : ℝ}
    (hc : BoundedDriftItoCharacteristics P V X d J β) (D : ℝ)
    (hD : ∀s ω, ‖d s ω‖ ≤ D) {a b : ℝ≥0} (hab : a ≤ b) (ω : Ω) :
    ‖integratedDrift d b ω-integratedDrift d a ω‖ ≤ D*((b:ℝ)-a) := by
  have hi (t : ℝ≥0) : IntervalIntegrable (fun s : ℝ => d s.toNNReal ω) volume 0 t := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le t.coe_nonneg).mpr
    apply (integrableOn_const isCompact_Icc.measure_ne_top (C := D)).mono'
    · exact ((hc.measurable_drift.comp
        (measurable_real_toNNReal.prodMk measurable_const)).aestronglyMeasurable)
    · exact .of_forall fun s => hD s.toNNReal ω
  have he (t : ℝ≥0) : integratedDrift d t ω=∫s in 0..(t:ℝ),d s.toNNReal ω := by
    rw [integratedDrift,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le t.coe_nonneg]
  rw [he a,he b,intervalIntegral.integral_interval_sub_left (hi b) (hi a)]
  simpa only [abs_of_nonneg (sub_nonneg.mpr (show (a:ℝ)≤b by exact_mod_cast hab))] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (a:ℝ)) (b := (b:ℝ)) (fun s _ => hD s.toNNReal ω)

 def optimalIncrementBound (β : ℝ) : ℝ := gradientTimeBound β+
    uniformSpatialConstant β 1*β^2+
    2*uniformSpatialConstant β 2*β^4+2*uniformSpatialConstant β 2

 theorem optimalIncrementBound_nonneg (β : ℝ) : 0 ≤ optimalIncrementBound β := by
  unfold optimalIncrementBound
  positivity [gradientTimeBound_nonneg β, (uniformSpatialConstant_pos β 1).le,
    (uniformSpatialConstant_pos β 2).le]

 theorem optimalMagnetization_increment_remainder (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ 1) (ω : BrownianSample) :
    ‖stoppedMagnetization β hβ μ b ω-stoppedMagnetization β hβ μ a ω-
      stoppedCurvature β hβ μ a ω*
      (canonicalDiracShiftMartingale β 0 b ω-canonicalDiracShiftMartingale β 0 a ω)‖ ≤
      optimalIncrementBound β*((b:ℝ)-a+
        (canonicalDiracShiftMartingale β 0 b ω-canonicalDiracShiftMartingale β 0 a ω)^2) := by
  let X := selectedParisiItoState β 0 hβ μ
  let J := canonicalDiracShiftMartingale β 0
  let d := selectedParisiItoDrift β 0 hβ μ
  let dt : ℝ := (b:ℝ)-a
  let A := integratedDrift d b ω-integratedDrift d a ω
  let B := J b ω-J a ω
  have hc := boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ
  have hd : ∀s ω, ‖d s ω‖ ≤ β^2 := norm_canonicalParisiItoDrift_le β 0 μ _ _ _ _
  have hA : ‖A‖ ≤ β^2*dt := norm_integratedDrift_sub_le hc (β^2) hd hab ω
  have hX : X b ω-X a ω=A+B := by
    have ha := hc.decomposition a ω
    have hbb := hc.decomposition b ω
    change X b ω=X 0 ω+integratedDrift d b ω+J b ω at hbb
    change X a ω=X 0 ω+integratedDrift d a ω+J a ω at ha
    dsimp [A,B]
    linarith
  have ha : a ≤ 1 := hab.trans hb
  have har : (a:ℝ)∈Icc (0:ℝ) 1 := ⟨a.coe_nonneg,by exact_mod_cast ha⟩
  have hbr : (b:ℝ)∈Icc (0:ℝ) 1 := ⟨b.coe_nonneg,by exact_mod_cast hb⟩
  have ht := parisiGradient_time_bound β hβ μ har hbr (X b ω)
  have hs := spatialGradient_remainder_le β μ a (X a ω) (X b ω)
  have hC : ‖parisiSpatialJet β μ 2 a (X a ω)‖ ≤ uniformSpatialConstant β 1 :=
    (norm_parisiSpatialJet_succ_le β μ 1 _ _).trans (norm_spatialDerivativeBCF_le_uniform β μ 1)
  have hdt : 0 ≤ dt := sub_nonneg.mpr (by exact_mod_cast hab)
  have hdt1 : dt ≤ 1 := by dsimp [dt];linarith [hbr.2,a.coe_nonneg]
  have hsp : ‖X b ω-X a ω‖^2 ≤ 2*B^2+2*β^4*dt := by
    rw [hX]
    have hn := norm_add_le A B
    have habs : ‖A+B‖ ≤ β^2*dt+‖B‖ := hn.trans (add_le_add hA le_rfl)
    have hsq := sq_le_sq₀ (norm_nonneg (A+B)) (by positivity : 0≤β^2*dt+‖B‖) |>.mpr habs
    have hdt2 : dt^2 ≤ dt := by nlinarith
    have hB : ‖B‖^2=B^2 := by simpa only [Real.norm_eq_abs] using sq_abs B
    calc
      ‖A+B‖^2 ≤ (β^2*dt+‖B‖)^2 := hsq
      _ ≤ 2*(β^2*dt)^2+2*‖B‖^2 := by nlinarith [sq_nonneg (β^2*dt-‖B‖)]
      _ = 2*β^4*dt^2+2*B^2 := by rw [hB];ring
      _ ≤ 2*β^4*dt+2*B^2 := by gcongr
      _ = 2*B^2+2*β^4*dt := by ring
  change ‖stoppedMagnetization β hβ μ b ω-stoppedMagnetization β hβ μ a ω-
    stoppedCurvature β hβ μ a ω*B‖ ≤ optimalIncrementBound β*(dt+B^2)
  simp only [stoppedMagnetization,stoppedCurvature,min_eq_left ha,min_eq_left hb,
    selectedParisiGradientProcess]
  change ‖parisiGradient β μ (b,X b ω)-parisiGradient β μ (a,X a ω)-
    parisiSpatialJet β μ 2 a (X a ω)*B‖ ≤ _
  have he : parisiGradient β μ (b,X b ω)-parisiGradient β μ (a,X a ω)-
      parisiSpatialJet β μ 2 a (X a ω)*B =
      (parisiGradient β μ (b,X b ω)-parisiGradient β μ (a,X b ω))+
      (parisiSpatialJet β μ 1 a (X b ω)-parisiSpatialJet β μ 1 a (X a ω)-
        parisiSpatialJet β μ 2 a (X a ω)*(X b ω-X a ω))+
      parisiSpatialJet β μ 2 a (X a ω)*A := by rw [parisiSpatialJet_one,parisiSpatialJet_one,hX];ring
  rw [he]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  have htt : ‖parisiGradient β μ (b,X b ω)-parisiGradient β μ (a,X b ω)‖ ≤ gradientTimeBound β*dt := by
    change _ ≤ gradientTimeBound β*‖dt‖ at ht
    rwa [Real.norm_of_nonneg hdt] at ht
  have hsa := hs.trans (mul_le_mul_of_nonneg_left hsp (uniformSpatialConstant_pos β 2).le)
  have hca : ‖parisiSpatialJet β μ 2 a (X a ω)*A‖ ≤ uniformSpatialConstant β 1*β^2*dt := by
    rw [norm_mul]
    exact (mul_le_mul hC hA (norm_nonneg _) (uniformSpatialConstant_pos β 1).le).trans_eq (by ring)
  have hsum := add_le_add (add_le_add htt hsa) hca
  apply hsum.trans
  unfold optimalIncrementBound
  have hp1 := (uniformSpatialConstant_pos β 1).le
  have hp2 := (uniformSpatialConstant_pos β 2).le
  have hgt := gradientTimeBound_nonneg β
  nlinarith [sq_nonneg B, mul_nonneg hgt (sq_nonneg B),
    mul_nonneg (mul_nonneg hp1 (sq_nonneg β)) (sq_nonneg B),
    mul_nonneg (mul_nonneg hp2 (by positivity : 0≤β^4)) (sq_nonneg B),
    mul_nonneg hp2 hdt]

end FRSB
