module

public import FRSB.StoppedOptimalProcess
public import FRSB.BrownianCrossRemainder
public import FRSB.GammaPrime
public import Paper.WeightedDrift

@[expose] public section

/-! Exact second moments and continuous Riemann limits of the actual optimal
curvature's uniform Brownian left sums. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter StochasticCalculus
open scoped NNReal ENNReal Topology BigOperators
namespace FRSB

def optimalMLeftSum (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (T : ℝ≥0) (n : ℕ)
    (sample : BrownianSample) : ℝ :=
  uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β 0)
    (stoppedCurvature β hβ μ) T (n+1) T sample

theorem uniform_left_riemann_tendsto (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ≥0) :
    Tendsto (fun n => ∑i ∈ Finset.range (n+1),
      f (uniformPartitionTime T (n+1) i) *
        ((uniformPartitionTime T (n+1) (i+1) : ℝ)-uniformPartitionTime T (n+1) i))
      atTop (𝓝 (∫s in (0:ℝ)..(T:ℝ),f s)) := by
  let w : ℝ≥0 → ℝ := fun s => f s
  have hw : Continuous w := hf.comp NNReal.continuous_coe
  have h1 : IntegrableOn (fun _ : ℝ≥0 => (1:ℝ)) (Ioc 0 T) nonnegativeLebesgueMeasure :=
    integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)
  have hwint : IntegrableOn w (Ioc 0 T) nonnegativeLebesgueMeasure :=
    ((hw.continuousOn.integrableOn_compact isCompact_Icc)
      : IntegrableOn w (Icc 0 T) nonnegativeLebesgueMeasure).mono_set Ioc_subset_Icc_self
  have hl := uniformPartition_weighted_integral_tendsto (fun _ : ℝ≥0 => (1:ℝ)) w T h1
    (by simpa only [mul_one] using hwint) (fun _ => by norm_num) hw.continuousOn
  have hint (r : ℝ≥0) : (∫s in Ioc (0:ℝ≥0) r,(1:ℝ) ∂nonnegativeLebesgueMeasure) = (r:ℝ) := by
    simp [integral_const,Measure.real,nonnegativeLebesgueMeasure_Ioc]
  have htarget : (∫s in Ioc (0:ℝ≥0) T,w s ∂nonnegativeLebesgueMeasure) =
      ∫s in (0:ℝ)..(T:ℝ),f s := by
    rw [integral_nonnegative_Ioc_eq_real_Icc (fun s (_ : Unit) => w s) T (),
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le T.coe_nonneg]
    apply intervalIntegral.integral_congr
    intro s hs
    change f (s.toNNReal:ℝ) = f s
    rw [Real.coe_toNNReal s ((uIcc_of_le T.coe_nonneg ▸ hs).1)]
  simpa only [mul_one,hint,w,htarget] using hl

theorem martingale_scaled_canonicalBrownian (β : ℝ) :
    Martingale (canonicalDiracShiftMartingale β 0) canonicalBrownianFiltration canonicalBrownianMeasure := by
  have hF : canonicalBrownianShiftFiltration 0 = canonicalBrownianFiltration := by
    apply Filtration.ext
    funext t
    change canonicalBrownianFiltration (0+t) = canonicalBrownianFiltration t
    rw [zero_add]
  rw [← hF]
  exact martingale_canonicalDiracShiftMartingale β 0

theorem memLp_optimalMLeftSum (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (T : ℝ≥0) (n : ℕ) :
    MemLp (optimalMLeftSum β hβ μ T n) 2 canonicalBrownianMeasure := by
  let J := canonicalDiracShiftMartingale β 0
  let H := stoppedCurvature β hβ μ
  have hJ := memLp_canonicalDiracShiftMartingale β 0
  have hi (i : ℕ) : MemLp (fun sample => H (uniformPartitionTime T (n+1) i) sample*
      (J (uniformPartitionTime T (n+1) (i+1)) sample-J (uniformPartitionTime T (n+1) i) sample))
      2 canonicalBrownianMeasure := by
    apply memLp_two_mul_bounded _ _
      (((stronglyAdapted_stoppedCurvature β hβ μ _).mono
        (canonicalBrownianFiltration.le _)).aestronglyMeasurable)
      ((hJ _).sub (hJ _)) (uniformSpatialConstant β 1).toNNReal
    intro sample
    rw [Real.coe_toNNReal _ (uniformSpatialConstant_pos β 1).le]
    exact norm_stoppedCurvature_le β hβ μ _ sample
  have hs := memLp_finsetSum (Finset.range (n+1)) (fun i _ => hi i)
  refine MemLp.ae_eq ?_ hs
  exact .of_forall fun sample => by
    simp only [optimalMLeftSum,uniformAdaptedMartingaleLeftSumProcess_terminal,J,H]

theorem optimalMLeftSum_secondMoment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) (n : ℕ) :
    (∫sample,(optimalMLeftSum β hβ μ T n sample)^2 ∂canonicalBrownianMeasure) =
    ∑i ∈ Finset.range (n+1),
      gammaCurvatureSource β hβ μ μ (uniformPartitionTime T (n+1) i)*
        ((uniformPartitionTime T (n+1) (i+1):ℝ)-uniformPartitionTime T (n+1) i) := by
  change (∫sample, (uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β 0)
    (stoppedCurvature β hβ μ) T (n+1) T sample)^2 ∂canonicalBrownianMeasure) = _
  rw [integral_sq_uniformAdaptedMartingaleLeftSumProcess_terminal
    (martingale_scaled_canonicalBrownian β)
    (memLp_canonicalDiracShiftMartingale β 0)
    (stronglyAdapted_stoppedCurvature β hβ μ) (uniformSpatialConstant β 1).toNNReal
    (fun t sample => by
      rw [Real.coe_toNNReal _ (uniformSpatialConstant_pos β 1).le]
      exact norm_stoppedCurvature_le β hβ μ t sample)]
  apply Finset.sum_congr rfl
  intro i hi
  have ha := uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
    (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hab := monotone_uniformPartitionTime_general T (n+1) (Nat.le_succ i)
  have he := integral_square_known_scaledBrownian_increment β _ _ hab
    (stoppedCurvature β hβ μ (uniformPartitionTime T (n+1) i))
    (stronglyAdapted_stoppedCurvature β hβ μ _)
  have hJ (r : ℝ≥0) (sample : BrownianSample) :
      canonicalDiracShiftMartingale β 0 r sample = β*canonicalBrownian r sample := by
    simp [canonicalDiracShiftMartingale]
  simp_rw [hJ,← mul_sub] at *
  rw [he,gammaCurvatureSource_self β hβ μ
    ⟨by positivity,by exact_mod_cast ha.2.trans hT⟩]
  have hC : (∫sample,stoppedCurvature β hβ μ (uniformPartitionTime T (n+1) i) sample^2
      ∂canonicalBrownianMeasure) = curvatureMoment2 β μ (uniformPartitionTime T (n+1) i) := by
    unfold curvatureMoment2
    apply integral_congr_ae
    exact .of_forall fun sample => by
      dsimp only
      rw [stoppedCurvature_eq_physical β hβ μ (ha.2.trans hT)]
  rw [hC]
  ring

theorem tendsto_optimalMLeftSum_secondMoment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1) :
    Tendsto (fun n => ∫sample,(optimalMLeftSum β hβ μ T n sample)^2 ∂canonicalBrownianMeasure)
      atTop (𝓝 (∫s in (0:ℝ)..(T:ℝ),gammaCurvatureSource β hβ μ μ s)) := by
  simp_rw [optimalMLeftSum_secondMoment β hβ μ T hT]
  exact uniform_left_riemann_tendsto _ (continuous_gammaCurvatureSource β hβ μ μ) T

end FRSB
