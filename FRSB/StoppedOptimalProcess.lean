module

public import FRSB.PolynomialMomentConvergence
public import FRSB.ConstantMassParity
public import Paper.ParisiGradientMartingaleLaw

@[expose] public section

/-! Genuine globally stopped optimal-gradient and curvature processes in the
original full Brownian filtration. The stopping is deterministic at time one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 600000

 def stoppedMagnetization (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  selectedParisiGradientProcess β 0 hβ μ (min t 1) ω

 def stoppedCurvature (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  parisiSpatialJet β μ 2 ((min t 1 : ℝ≥0) : ℝ)
    (selectedParisiItoState β 0 hβ μ (min t 1) ω)

 theorem stronglyAdapted_stoppedMagnetization (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    StronglyAdapted canonicalBrownianFiltration (stoppedMagnetization β hβ μ) :=
  fun t => (stronglyAdapted_selectedParisiGradientProcess β 0 hβ μ (min t 1)).mono
    (canonicalBrownianFiltration.mono (min_le_left _ _))

 theorem norm_stoppedMagnetization_le_one (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) : ‖stoppedMagnetization β hβ μ t ω‖ ≤ 1 :=
  norm_parisiGradient_le_one β μ _

 theorem memLp_stoppedMagnetization (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (t : ℝ≥0) :
    MemLp (stoppedMagnetization β hβ μ t) 2 canonicalBrownianMeasure :=
  MemLp.of_bound (((stronglyAdapted_stoppedMagnetization β hβ μ t).mono
    (canonicalBrownianFiltration.le t)).aestronglyMeasurable) 1
    (.of_forall (norm_stoppedMagnetization_le_one β hβ μ t))

 theorem martingale_stoppedMagnetization (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    Martingale (stoppedMagnetization β hβ μ) canonicalBrownianFiltration canonicalBrownianMeasure := by
  refine ⟨stronglyAdapted_stoppedMagnetization β hβ μ,?_⟩
  intro r t hrt
  change canonicalBrownianMeasure[selectedParisiGradientProcess β 0 hβ μ (min t 1) |
    canonicalBrownianFiltration r] =ᵐ[canonicalBrownianMeasure]
    selectedParisiGradientProcess β 0 hβ μ (min r 1)
  by_cases hr : r ≤ 1
  · by_cases ht : t ≤ 1
    · simpa only [min_eq_left hr,min_eq_left ht] using
        condExp_selectedParisiGradientProcess β 0 hβ μ r t hrt (by exact_mod_cast ht)
    · simpa only [min_eq_left hr,min_eq_right (le_of_not_ge ht)] using
        condExp_selectedParisiGradientProcess β 0 hβ μ r 1 hr (by norm_num)
  · have hr1 : 1 ≤ r := le_of_not_ge hr
    have ht1 : 1 ≤ t := hr1.trans hrt
    simp only [min_eq_right hr1,min_eq_right ht1]
    rw [condExp_of_stronglyMeasurable (canonicalBrownianFiltration.le r)
      ((stronglyAdapted_selectedParisiGradientProcess β 0 hβ μ 1).mono
        (canonicalBrownianFiltration.mono hr1))
      (integrable_selectedParisiGradientProcess β 0 hβ μ 1)]

 theorem stronglyAdapted_stoppedCurvature (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    StronglyAdapted canonicalBrownianFiltration (stoppedCurvature β hβ μ) := by
  intro t
  change StronglyMeasurable[canonicalBrownianFiltration t]
    (fun ω => parisiSpatialJet β μ 2 ((min t 1 : ℝ≥0) : ℝ)
      (selectedParisiItoState β 0 hβ μ (min t 1) ω))
  have hX : StronglyMeasurable[canonicalBrownianFiltration t]
      (selectedParisiItoState β 0 hβ μ (min t 1)) :=
    ((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state (min t 1)).mono
      (canonicalBrownianFiltration.mono (min_le_left _ _))
  have hfun : Continuous (fun x : ℝ => parisiSpatialJet β μ 2
      ((min t 1 : ℝ≥0) : ℝ) x) :=
    (continuous_parisiSpatialJet_succ β μ 1).comp
      (continuous_const.prodMk continuous_id)
  exact hfun.comp_stronglyMeasurable hX

 theorem norm_stoppedCurvature_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (ω : BrownianSample) :
    ‖stoppedCurvature β hβ μ t ω‖ ≤ uniformSpatialConstant β 1 :=
  (norm_parisiSpatialJet_succ_le β μ 1 _ _).trans (norm_spatialDerivativeBCF_le_uniform β μ 1)

 theorem stoppedMagnetization_eq_physical (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {t : ℝ≥0} (ht : t ≤ 1) (ω : BrownianSample) :
    stoppedMagnetization β hβ μ t ω=M β μ t ω := by
  simp only [stoppedMagnetization,min_eq_left ht,selectedParisiGradientProcess,
    M,jetProcess,parisiSpatialJet_one]
  rw [selectedParisiItoState_eq β 0 hβ μ (by exact_mod_cast ht)]
  rfl

 theorem stoppedCurvature_eq_physical (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {t : ℝ≥0} (ht : t ≤ 1) (ω : BrownianSample) :
    stoppedCurvature β hβ μ t ω=C β μ t ω := by
  simp only [stoppedCurvature,min_eq_left ht,C,jetProcess]
  rw [selectedParisiItoState_eq β 0 hβ μ (by exact_mod_cast ht)]
  rfl

@[simp] theorem stoppedMagnetization_initial (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (ω : BrownianSample) : stoppedMagnetization β hβ μ 0 ω=0 := by
  rw [stoppedMagnetization_eq_physical β hβ μ (by norm_num)]
  simp only [M,jetProcess,NNReal.coe_zero,optimalState_initial,parisiSpatialJet_one]
  exact parisiGradient_at_zero β hβ μ 0 ⟨le_rfl,by norm_num⟩

end FRSB
