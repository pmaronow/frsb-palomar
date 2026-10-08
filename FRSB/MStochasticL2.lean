module

public import FRSB.MStochasticCross
public import FRSB.GammaEndpoints

@[expose] public section

/-! The actual arbitrary-measure stochastic equation dM=beta C dW.
The stochastic integral is characterized by genuine uniform adapted left sums,
with convergence in L2 (and hence in probability), not by an assumed identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FRSB

theorem optimalMagnetization_secondMoment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) :
    (∫sample,(stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample)^2
      ∂canonicalBrownianMeasure) = ∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s := by
  simp only [stoppedMagnetization_initial,sub_zero]
  have hM : (∫sample,stoppedMagnetization β hβ μ T sample^2 ∂canonicalBrownianMeasure) =
      Gamma β μ T := by
    unfold Gamma
    apply integral_congr_ae
    exact .of_forall fun sample => by
      dsimp only
      rw [stoppedMagnetization_eq_physical β hβ μ hT]
  rw [hM,Gamma_integral β hβ μ ⟨T.coe_nonneg,by exact_mod_cast hT⟩,
    Gamma_initial_zero β hβ μ,zero_add]

theorem optimalMLeftSum_error_square_expansion (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) (n : ℕ) :
    (∫sample,(stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample-
        optimalMLeftSum β hβ μ T n sample)^2 ∂canonicalBrownianMeasure) =
    (∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s) -
      2*(∫sample,(stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample)*
        optimalMLeftSum β hβ μ T n sample ∂canonicalBrownianMeasure) +
      (∫sample,(optimalMLeftSum β hβ μ T n sample)^2 ∂canonicalBrownianMeasure) := by
  let U := fun sample => stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample
  let S := optimalMLeftSum β hβ μ T n
  have hU : MemLp U 2 canonicalBrownianMeasure :=
    (memLp_stoppedMagnetization β hβ μ T).sub (memLp_stoppedMagnetization β hβ μ 0)
  have hS : MemLp S 2 canonicalBrownianMeasure := memLp_optimalMLeftSum β hβ μ T n
  have hiU : Integrable (fun sample => U sample^2) canonicalBrownianMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using hU.integrable_norm_pow'
  have hiS : Integrable (fun sample => S sample^2) canonicalBrownianMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using hS.integrable_norm_pow'
  have hiUS : Integrable (fun sample => U sample*S sample) canonicalBrownianMeasure :=
    memLp_one_iff_integrable.mp (hU.mul hS)
  have he1 : (∫sample,U sample^2-2*(U sample*S sample)+S sample^2 ∂canonicalBrownianMeasure) =
      (∫sample,U sample^2-2*(U sample*S sample) ∂canonicalBrownianMeasure)+
        (∫sample,S sample^2 ∂canonicalBrownianMeasure) :=
    integral_add (hiU.sub (hiUS.const_mul 2)) hiS
  have he2 : (∫sample,U sample^2-2*(U sample*S sample) ∂canonicalBrownianMeasure) =
      (∫sample,U sample^2 ∂canonicalBrownianMeasure)-
        2*(∫sample,U sample*S sample ∂canonicalBrownianMeasure) := by
    rw [integral_sub hiU (hiUS.const_mul 2),integral_const_mul]
  have he : (fun sample => (U sample-S sample)^2) =
      fun sample => U sample^2-2*(U sample*S sample)+S sample^2 := by funext sample;ring
  change (∫sample,(U sample-S sample)^2 ∂canonicalBrownianMeasure) = _
  rw [he,he1,he2,optimalMagnetization_secondMoment β hβ μ T hT]

theorem tendsto_optimalMLeftSum_L2 (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) :
    Tendsto (fun n => ∫sample,(stoppedMagnetization β hβ μ T sample-
      stoppedMagnetization β hβ μ 0 sample-optimalMLeftSum β hβ μ T n sample)^2
      ∂canonicalBrownianMeasure) atTop (𝓝 0) := by
  simp_rw [optimalMLeftSum_error_square_expansion β hβ μ T hT]
  have hc := tendsto_optimalM_cross_moment β hβ μ T hT
  have hs := tendsto_optimalMLeftSum_secondMoment β hβ μ T hT
  have hh := ((tendsto_const_nhds (x := ∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s)).sub
    (hc.const_mul 2)).add hs
  have hz : (∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s)-
      2*(∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s)+
      (∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s) = 0 := by ring
  simpa only [hz] using hh

/-- L2 convergence of these square-integrable actual sums implies convergence
in probability by the genuine second-moment Markov inequality. -/
theorem tendstoInMeasure_optimalMLeftSum (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) :
    TendstoInMeasure canonicalBrownianMeasure (optimalMLeftSum β hβ μ T) atTop
      (fun sample => stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  let U := fun sample => stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample
  have hU : MemLp U 2 canonicalBrownianMeasure :=
    (memLp_stoppedMagnetization β hβ μ T).sub (memLp_stoppedMagnetization β hβ μ 0)
  have hi (n : ℕ) : Integrable (fun sample => (optimalMLeftSum β hβ μ T n sample-U sample)^2)
      canonicalBrownianMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using
      ((memLp_optimalMLeftSum β hβ μ T n).sub hU).integrable_norm_pow'
  have he (n : ℕ) : (∫sample,(optimalMLeftSum β hβ μ T n sample-U sample)^2
      ∂canonicalBrownianMeasure) = ∫sample,(U sample-optimalMLeftSum β hβ μ T n sample)^2
      ∂canonicalBrownianMeasure := by
    apply integral_congr_ae
    exact .of_forall fun sample => by dsimp only;ring
  have hbound (n : ℕ) : canonicalBrownianMeasure.real
      {sample | ε ≤ ‖optimalMLeftSum β hβ μ T n sample-U sample‖} ≤
      (∫sample,(U sample-optimalMLeftSum β hβ μ T n sample)^2
        ∂canonicalBrownianMeasure)/ε^2 := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ:=canonicalBrownianMeasure) (Filter.Eventually.of_forall
        (fun sample => sq_nonneg (optimalMLeftSum β hβ μ T n sample-U sample))) (hi n) (ε^2)
    have hset : {sample | ε ≤ ‖optimalMLeftSum β hβ μ T n sample-U sample‖} ⊆
        {sample | ε^2 ≤ (optimalMLeftSum β hβ μ T n sample-U sample)^2} := by
      intro sample hs
      have hh := sq_le_sq₀ hε.le (norm_nonneg _) |>.mpr hs
      change ε^2 ≤ (optimalMLeftSum β hβ μ T n sample-U sample)^2
      simpa only [Real.norm_eq_abs,sq_abs] using hh
    have hm := measureReal_mono (μ := canonicalBrownianMeasure) hset
    have hp := mul_le_mul_of_nonneg_left hm (sq_nonneg ε)
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    rw [mul_comm]
    exact (hp.trans h).trans_eq (he n)
  apply squeeze_zero (fun _ => measureReal_nonneg) hbound
  simpa only [zero_div] using (tendsto_optimalMLeftSum_L2 β hβ μ T hT).div_const (ε^2)

/-- Literal arbitrary-measure zero-field stochastic display of Lemma 2.5,
with the actual physical M at the limit. -/
theorem optimalM_stochastic_identity (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) :
    TendstoInMeasure canonicalBrownianMeasure (optimalMLeftSum β hβ μ T) atTop
      (M β μ T) := by
  have hh := tendstoInMeasure_optimalMLeftSum β hβ μ T hT
  apply TendstoInMeasure.congr_right _ hh
  exact .of_forall fun sample => by
    simp only [stoppedMagnetization_initial,sub_zero]
    exact stoppedMagnetization_eq_physical β hβ μ hT sample

end FRSB
