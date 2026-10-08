module

public import FRSB.MStochasticSum
public import FRSB.OptimalIncrementRemainder

@[expose] public section

/-! Quantitative convergence of the actual martingale/Brownian cross term. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FRSB
set_option maxHeartbeats 800000

def optimalMCrossErrorConstant (β : ℝ) : ℝ :=
  optimalIncrementBound β * uniformSpatialConstant β 1 * brownianCrossRemainderConstant β

theorem optimalMCrossErrorConstant_nonneg (β : ℝ) : 0 ≤ optimalMCrossErrorConstant β := by
  unfold optimalMCrossErrorConstant brownianCrossRemainderConstant
  positivity [optimalIncrementBound_nonneg β,(uniformSpatialConstant_pos β 1).le]

theorem optimalM_cross_cell_bound (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {a b : ℝ≥0} (hab : a ≤ b) (hb : b ≤ 1) :
    ‖(∫sample,(stoppedMagnetization β hβ μ b sample-stoppedMagnetization β hβ μ a sample)*
        stoppedCurvature β hβ μ a sample*
        (canonicalDiracShiftMartingale β 0 b sample-canonicalDiracShiftMartingale β 0 a sample)
        ∂canonicalBrownianMeasure) -
      (∫sample,(stoppedCurvature β hβ μ a sample*
        (canonicalDiracShiftMartingale β 0 b sample-canonicalDiracShiftMartingale β 0 a sample))^2
        ∂canonicalBrownianMeasure)‖ ≤
    optimalMCrossErrorConstant β*((b:ℝ)-a)*Real.sqrt ((b:ℝ)-a) := by
  let J := canonicalDiracShiftMartingale β 0
  let H := stoppedCurvature β hβ μ a
  let D := fun sample => stoppedMagnetization β hβ μ b sample-stoppedMagnetization β hβ μ a sample
  let Z := fun sample => J b sample-J a sample
  let d : ℝ := (b:ℝ)-a
  let K := uniformSpatialConstant β 1
  have hd : 0 ≤ d := sub_nonneg.mpr (show (a:ℝ) ≤ b from hab)
  have hZ : MemLp Z 2 canonicalBrownianMeasure :=
    (memLp_canonicalDiracShiftMartingale β 0 b).sub (memLp_canonicalDiracShiftMartingale β 0 a)
  have hH : AEStronglyMeasurable H canonicalBrownianMeasure := ((stronglyAdapted_stoppedCurvature β hβ μ a).mono
    (canonicalBrownianFiltration.le a)).aestronglyMeasurable
  have hA : MemLp (fun sample => H sample*Z sample) 2 canonicalBrownianMeasure := by
    apply memLp_two_mul_bounded _ _ hH hZ K.toNNReal
    intro sample
    rw [Real.coe_toNNReal _ (uniformSpatialConstant_pos β 1).le]
    exact norm_stoppedCurvature_le β hβ μ a sample
  have hD : MemLp D 2 canonicalBrownianMeasure :=
    (memLp_stoppedMagnetization β hβ μ b).sub (memLp_stoppedMagnetization β hβ μ a)
  have hDA : Integrable (fun sample => D sample*(H sample*Z sample)) canonicalBrownianMeasure :=
    memLp_one_iff_integrable.mp (hD.mul hA)
  have hA2 : Integrable (fun sample => (H sample*Z sample)^2) canonicalBrownianMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs] using hA.integrable_norm_pow'
  have hZeq (sample : BrownianSample) : Z sample=β*(canonicalBrownian b sample-canonicalBrownian a sample) := by
    dsimp [Z,J,canonicalDiracShiftMartingale]
    simp only [zero_add]
    ring
  have hmoment : Integrable (fun sample => |Z sample| *(d+Z sample^2)) canonicalBrownianMeasure := by
    have hiabs := (hZ.integrable (by norm_num)).norm
    have h3 : MemLp Z 3 canonicalBrownianMeasure := by
      have hl := (hasLaw_scaledBrownian_increment β a b hab).hasGaussianLaw.memLp (p := (3:ℝ≥0∞)) (by norm_num)
      exact MemLp.ae_eq (.of_forall fun sample => (hZeq sample).symm) hl
    have hi3 := h3.integrable_norm_pow'
    convert (hiabs.mul_const d).add hi3 using 1
    funext sample
    simp only [Pi.add_apply,Real.norm_eq_abs]
    rw [← sq_abs (Z sample)]
    ring
  have he : (∫sample,D sample*(H sample*Z sample) ∂canonicalBrownianMeasure)-
      (∫sample,(H sample*Z sample)^2 ∂canonicalBrownianMeasure) =
      ∫sample,(D sample-H sample*Z sample)*(H sample*Z sample) ∂canonicalBrownianMeasure := by
    rw [← integral_sub hDA hA2]
    apply integral_congr_ae
    exact .of_forall fun sample => by dsimp only;ring
  change ‖(∫sample,D sample*H sample*Z sample ∂canonicalBrownianMeasure)-
    (∫sample,(H sample*Z sample)^2 ∂canonicalBrownianMeasure)‖ ≤ _
  simp_rw [mul_assoc]
  rw [he]
  have hiupper := hmoment.const_mul (optimalIncrementBound β*K)
  have hn := norm_integral_le_of_norm_le
    (f := fun sample => (D sample-H sample*Z sample)*(H sample*Z sample)) hiupper (Filter.Eventually.of_forall fun sample => by
    rw [norm_mul,norm_mul,Real.norm_eq_abs (Z sample)]
    have hr := optimalMagnetization_increment_remainder β hβ μ hab hb sample
    change ‖D sample-H sample*Z sample‖ ≤ optimalIncrementBound β*(d+Z sample^2) at hr
    have hc := norm_stoppedCurvature_le β hβ μ a sample
    change ‖H sample‖ ≤ K at hc
    have hh := mul_le_mul hr hc (norm_nonneg _) (by
      positivity [optimalIncrementBound_nonneg β] : 0 ≤ optimalIncrementBound β*(d+Z sample^2))
    have hh' := mul_le_mul_of_nonneg_right hh (abs_nonneg (Z sample))
    calc
      ‖D sample-H sample*Z sample‖*(‖H sample‖*|Z sample|) =
          (‖D sample-H sample*Z sample‖*‖H sample‖)*|Z sample| := by ring
      _ ≤ (optimalIncrementBound β*(d+Z sample^2)*K)*|Z sample| := hh'
      _ = optimalIncrementBound β*K*(|Z sample| *(d+Z sample^2)) := by ring)
  apply hn.trans
  rw [integral_const_mul]
  have hm := integral_abs_scaledBrownian_cross_remainder β a b hab
  simp_rw [← hZeq] at hm
  have hc : 0 ≤ optimalIncrementBound β*K := mul_nonneg (optimalIncrementBound_nonneg β)
    (uniformSpatialConstant_pos β 1).le
  exact (mul_le_mul_of_nonneg_left hm hc).trans_eq (by
    unfold optimalMCrossErrorConstant
    dsimp only [K,d]
    ring)

theorem optimalM_cross_sum_bound (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) (n : ℕ) :
    ‖(∫sample,(stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample)*
        optimalMLeftSum β hβ μ T n sample ∂canonicalBrownianMeasure)-
      (∫sample,(optimalMLeftSum β hβ μ T n sample)^2 ∂canonicalBrownianMeasure)‖ ≤
    optimalMCrossErrorConstant β*T*Real.sqrt ((T:ℝ)/(n+1:ℕ)) := by
  let K := (uniformSpatialConstant β 1).toNNReal
  have hK : ∀t sample,‖stoppedCurvature β hβ μ t sample‖ ≤ K := by
    intro t sample
    rw [show (K:ℝ)=uniformSpatialConstant β 1 from Real.coe_toNNReal _ (uniformSpatialConstant_pos β 1).le]
    exact norm_stoppedCurvature_le β hβ μ t sample
  change ‖(∫sample,(stoppedMagnetization β hβ μ T sample-stoppedMagnetization β hβ μ 0 sample)*
    uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β 0)
      (stoppedCurvature β hβ μ) T (n+1) T sample ∂canonicalBrownianMeasure)-
    (∫sample,(uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β 0)
      (stoppedCurvature β hβ μ) T (n+1) T sample)^2 ∂canonicalBrownianMeasure)‖ ≤ _
  rw [integral_terminal_martingale_mul_uniformLeftSum (martingale_stoppedMagnetization β hβ μ)
    (martingale_scaled_canonicalBrownian β) (memLp_stoppedMagnetization β hβ μ)
    (memLp_canonicalDiracShiftMartingale β 0) (stronglyAdapted_stoppedCurvature β hβ μ) K hK,
    integral_sq_uniformAdaptedMartingaleLeftSumProcess_terminal (martingale_scaled_canonicalBrownian β)
      (memLp_canonicalDiracShiftMartingale β 0) (stronglyAdapted_stoppedCurvature β hβ μ) K hK,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (le_trans (b := ∑_i ∈ Finset.range (n+1), optimalMCrossErrorConstant β*((T:ℝ)/(n+1:ℕ))*
    Real.sqrt ((T:ℝ)/(n+1:ℕ))) ?_ ?_)
  · apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hb := uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) (by omega : i+1 ≤ n+1)
    have hab := monotone_uniformPartitionTime_general T (n+1) (Nat.le_succ i)
    have h := optimalM_cross_cell_bound β hβ μ hab (hb.2.trans hT)
    have hd : (uniformPartitionTime T (n+1) (i+1):ℝ)-uniformPartitionTime T (n+1) i =
        (T:ℝ)/(n+1:ℕ) := by
      simp only [uniformPartitionTime,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast]
      have hn : (n+1:ℕ)≠0 := by positivity
      field_simp
      push_cast
      ring
    simpa only [hd] using h
  · rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have hn : (n+1:ℕ)≠0 := by positivity
    field_simp
    exact le_rfl

 theorem tendsto_optimalM_cross_moment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) :
    Tendsto (fun n => ∫sample,(stoppedMagnetization β hβ μ T sample-
      stoppedMagnetization β hβ μ 0 sample)*optimalMLeftSum β hβ μ T n sample
      ∂canonicalBrownianMeasure) atTop
      (𝓝 (∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s)) := by
  have hbound : Tendsto (fun n : ℕ => optimalMCrossErrorConstant β*T*
      Real.sqrt ((T:ℝ)/(n+1:ℕ))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ => (T:ℝ)/(n+1:ℕ)) atTop (𝓝 0) := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (T:ℝ)
      simpa only [mul_zero,div_eq_mul_inv,one_mul,Nat.cast_add,Nat.cast_one] using hh
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hdiv).const_mul (optimalMCrossErrorConstant β*T)
  have he := squeeze_zero_norm (fun n => optimalM_cross_sum_bound β hβ μ T hT n) hbound
  have hs := tendsto_optimalMLeftSum_secondMoment β hβ μ T hT
  have hc := he.add hs
  simpa only [sub_add_cancel,zero_add] using hc

end FRSB
