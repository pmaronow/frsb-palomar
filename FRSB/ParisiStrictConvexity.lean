module

public import FRSB.GammaIdentity
public import FRSB.ParisiStrictnessBridge
public import FRSB.ParisiMinimizerGeometry

@[expose] public section

/-! Genuine measure strict convexity and uniqueness of the zero-field Parisi
minimizer. The actual Gamma evolution discharges the analytic input of the
Jensen/martingale covariance detection bridge. -/
noncomputable section
open Set MeasureTheory
namespace FRSB
open Paper

/-- Equality in an interior measure mixture forces the actual measures equal. -/
theorem measure_eq_of_parisiPDEFunctional_mix_eq
    (β : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : parisiPDEFunctional β 0 (parisiMix μ ν t) =
      (1-t) * parisiPDEFunctional β 0 μ + t * parisiPDEFunctional β 0 ν) : μ = ν := by
  let ρ := parisiMix μ ν t
  apply measure_eq_of_mix_equality_of_momentDerivative β 0 hβ μ ν t ht
    (fun s => β ^ 2 * curvatureMoment2 β ρ s)
  · intro s hs
    have hfun : Gamma β ρ = selectedParisiSecondMoment β 0 hβ ρ :=
      funext (Gamma_eq_selectedSecondMoment β hβ ρ)
    rw [← hfun]
    exact hasDerivAt_Gamma β hβ ρ hs
  · intro s hs
    have hc := curvatureMoment2_pos β hβ ρ ⟨hs.1.le, hs.2.le⟩
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_of_nonneg hc.le]
    exact (mul_le_mul_of_nonneg_left
      (curvatureMoment2_le_one β hβ ρ ⟨hs.1.le, hs.2.le⟩) (sq_nonneg β)).trans_eq (mul_one _)
  · intro s hs
    exact (mul_pos (sq_pos_of_ne_zero hβ)
      (curvatureMoment2_pos β hβ ρ ⟨hs.1.le, hs.2.le⟩)).ne'
  · exact he

/-- The actual zero-field functional is strictly convex in probability mixtures. -/
theorem parisiPDEFunctional_mix_lt (β : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) (hne : μ ≠ ν) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    parisiPDEFunctional β 0 (parisiMix μ ν t) <
      (1-t) * parisiPDEFunctional β 0 μ + t * parisiPDEFunctional β 0 ν := by
  have hle := parisiPDEFunctional_mix_le β 0 μ ν t ⟨ht.1.le, ht.2.le⟩
  by_contra hnot
  exact hne (measure_eq_of_parisiPDEFunctional_mix_eq β hβ μ ν t ht
    (le_antisymm hle (not_lt.mp hnot)))

/-- Any two actual zero-field minimizing measures agree. -/
theorem IsParisiMinimizer.eq_zeroField {β : ℝ} (hβ : β ≠ 0) {μ ν : ParisiMeasure}
    (hμ : IsParisiMinimizer β 0 μ) (hν : IsParisiMinimizer β 0 ν) : μ = ν := by
  by_contra hne
  have hs := parisiPDEFunctional_mix_lt β hβ μ ν hne (1/2) (by norm_num)
  rw [hμ.mix_value hν (1/2) (by norm_num)] at hs
  exact (lt_irrefl _) hs

/-- Actual uniqueness of the selected minimizing law, with no supplied
strictness, PDE, stochastic-law, or moment identity hypothesis. -/
theorem parisiMinimizer_unique (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hμ : IsParisiMinimizer β 0 μ) : μ = parisiMinimizer β 0 :=
  hμ.eq_zeroField hβ (isParisiMinimizer_selected β 0)

/-- The cited zero-field Parisi-minimizer background claim is fully proved. -/
theorem existsUnique_parisi_minimizer (β : ℝ) (hβ : β ≠ 0) :
    ∃! μ : ParisiMeasure, IsParisiMinimizer β 0 μ := by
  exact ⟨parisiMinimizer β 0, isParisiMinimizer_selected β 0,
    fun μ hμ => parisiMinimizer_unique β hβ μ hμ⟩

end FRSB
