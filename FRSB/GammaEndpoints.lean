module

public import FRSB.OptimalDiffusion
public import FRSB.ConstantMassParity
public import Paper.ParisiMixContinuity

@[expose] public section

/-! Genuine endpoint bounds for the zero-field optimal diffusion moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace FRSB

theorem Gamma_initial_zero (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Gamma β μ 0 = 0 := by
  simp only [Gamma, M, jetProcess, optimalState_initial, parisiSpatialJet_one]
  simp only [parisiGradient_at_zero β hβ μ (0 : ℝ) (by norm_num), zero_pow (by decide : 2 ≠ 0),
    integral_zero]

theorem measurable_M (β : ℝ) (μ : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : Measurable (M β μ t) := by
  have htNN : (t.toNNReal : ℝ) ≤ 1 := by rw [Real.coe_toNNReal t ht.1]; exact ht.2
  have hstate : Measurable (fun sample => optimalStateReal β μ sample t) := by
    have hm := (Paper.measurable_canonicalParisiItoState β 0 μ
      (fun s x => Paper.parisiGradient β μ (s, x))
      (Paper.continuous_parisiGradient β μ)
      (fun s x => Paper.norm_parisiGradient_le_one β μ (s, x))
      (Paper.lipschitzWith_parisiGradient_all β μ)).comp
      ((measurable_const : Measurable (fun _ : BrownianSample => t.toNNReal)).prodMk
        measurable_id)
    change Measurable (fun sample => optimalState β μ t.toNNReal sample) at hm
    convert hm using 1
    funext sample
    rw [optimalState_eq_real β μ htNN, Real.coe_toNNReal t ht.1]
  have heq : M β μ t = fun sample => Paper.parisiGradient β μ (t, optimalStateReal β μ sample t) := by
    funext sample
    exact parisiSpatialJet_one β μ t _
  rw [heq]
  exact (continuous_parisiGradient β μ).measurable.comp
    ((measurable_const : Measurable (fun _ : BrownianSample => t)).prodMk hstate)

theorem integrable_M_sq (β : ℝ) (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun sample => M β μ t sample ^ 2) canonicalBrownianMeasure := by
  apply (integrable_const (1 : ℝ)).mono' ((measurable_M β μ t ht).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun sample => by
    rw [norm_pow]
    apply pow_le_one₀ (norm_nonneg _) _
    simp only [M, jetProcess, parisiSpatialJet_one]
    exact norm_parisiGradient_le_one β μ _

theorem Gamma_terminal_lt_one (β : ℝ) (μ : ParisiMeasure) : Gamma β μ 1 < 1 := by
  have hterminal (sample : BrownianSample) :
      M β μ 1 sample = Real.tanh (optimalStateReal β μ sample 1) := by
    simp only [M, jetProcess, parisiSpatialJet_one, parisiGradient_terminal]
  have hpos (sample : BrownianSample) : 0 < 1 - M β μ 1 sample ^ 2 := by
    rw [hterminal]
    have h := Real.abs_tanh_lt_one (optimalStateReal β μ sample 1)
    have ha := abs_nonneg (Real.tanh (optimalStateReal β μ sample 1))
    have hh := mul_self_lt_mul_self ha h
    nlinarith [sq_abs (Real.tanh (optimalStateReal β μ sample 1))]
  have hi : Integrable (fun sample => 1 - M β μ 1 sample ^ 2) canonicalBrownianMeasure :=
    (integrable_const _).sub (integrable_M_sq β μ 1 (by norm_num))
  have hs : Function.support (fun sample => 1 - M β μ 1 sample ^ 2) = univ := by
    ext sample
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hpos sample).ne'
  have hp : 0 < ∫ sample, 1 - M β μ 1 sample ^ 2 ∂canonicalBrownianMeasure :=
    (integral_pos_iff_support_of_nonneg (fun sample => (hpos sample).le) hi).mpr
      (by rw [hs]; simp)
  rw [integral_sub (integrable_const _) (integrable_M_sq β μ 1 (by norm_num)), integral_const] at hp
  simp only [probReal_univ, one_smul] at hp
  dsimp only [Gamma]
  linarith

end FRSB
