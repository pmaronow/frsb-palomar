module

public import FRSB.FiniteHistory

@[expose] public section

/-! Exact finite path density transport. Each transition is an actual density
relative to a Markov kernel, and the product retains every path coordinate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FRSB

def finiteHistoryDensity (w : ℕ → ℝ → ℝ → ℝ≥0∞) :
    (n : ℕ) → FiniteHistory n → ℝ≥0∞
  | 0 => fun _ => 1
  | n + 1 => fun p =>
      finiteHistoryDensity w n ((historySplit n p).1) *
        w n ((historySplit n p).1 (Fin.last n)) ((historySplit n p).2)

theorem measurable_finiteHistoryDensity (w : ℕ → ℝ → ℝ → ℝ≥0∞)
    (hw : ∀ n, Measurable (Function.uncurry (w n))) (n : ℕ) :
    Measurable (finiteHistoryDensity w n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp ((historySplit n).measurable.fst)).mul
      ((hw n).comp (((measurable_pi_apply _).comp (historySplit n).measurable.fst).prodMk
        (historySplit n).measurable.snd))

@[simp] theorem finiteHistoryDensity_snoc (w : ℕ → ℝ → ℝ → ℝ≥0∞)
    (n : ℕ) (p : FiniteHistory n) (y : ℝ) :
    finiteHistoryDensity w (n + 1) (Fin.snoc p y) =
      finiteHistoryDensity w n p * w n (p (Fin.last n)) y := by
  change finiteHistoryDensity w n ((historySplit n ((historySplit n).symm (p,y))).1) *
    w n ((historySplit n ((historySplit n).symm (p,y))).1 (Fin.last n))
      ((historySplit n ((historySplit n).symm (p,y))).2) = _
  simp only [MeasurableEquiv.apply_symm_apply]

theorem kernel_comap_withDensity {A : Type*} [MeasurableSpace A]
    (κ κ' : Kernel ℝ ℝ) [IsSFiniteKernel κ] (w : ℝ → ℝ → ℝ≥0∞)
    (hw : Measurable (Function.uncurry w)) (he : κ' = κ.withDensity w)
    (ρ : A → ℝ) (hρ : Measurable ρ) :
    κ'.comap ρ hρ = (κ.comap ρ hρ).withDensity (fun p y => w (ρ p) y) := by
  ext p : 1
  have hp : Measurable (Function.uncurry (fun p y => w (ρ p) y)) :=
    hw.comp (hρ.prodMap measurable_id)
  rw [Kernel.withDensity_apply _ hp]
  change κ' (ρ p) = (κ (ρ p)).withDensity (w (ρ p))
  rw [he, Kernel.withDensity_apply _ hw]

/-- The literal joint density of all states in a finite inhomogeneous Markov
chain is the product of its actual one-step transition densities. -/
theorem finiteHistoryLaw_withDensity (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (κ κ' : ℕ → Kernel ℝ ℝ) (hκ : ∀ n, IsMarkovKernel (κ n))
    (hκ' : ∀ n, IsMarkovKernel (κ' n)) (w : ℕ → ℝ → ℝ → ℝ≥0∞)
    (hw : ∀ n, Measurable (Function.uncurry (w n)))
    (he : ∀ n, κ' n = (κ n).withDensity (w n)) (n : ℕ) :
    finiteHistoryLaw ν κ' n =
      (finiteHistoryLaw ν κ n).withDensity (finiteHistoryDensity w n) := by
  induction n with
  | zero => exact (withDensity_one (μ := finiteHistoryLaw ν κ 0)).symm
  | succ n ih =>
    haveI := hκ n
    haveI := hκ' n
    haveI := isProbabilityMeasure_finiteHistoryLaw ν κ hκ n
    let ρ : FiniteHistory n → ℝ := fun p => p (Fin.last n)
    have hρ : Measurable ρ := measurable_pi_apply _
    have hmap := kernel_comap_withDensity (κ n) (κ' n) (w n) (hw n) (he n) ρ hρ
    haveI : IsSFiniteKernel (((κ n).comap ρ hρ).withDensity (fun p y => w n (ρ p) y)) := by
      rw [← hmap]
      infer_instance
    change (((finiteHistoryLaw ν κ' n) ⊗ₘ ((κ' n).comap ρ hρ)).map (historySplit n).symm) =
      (((finiteHistoryLaw ν κ n) ⊗ₘ ((κ n).comap ρ hρ)).map (historySplit n).symm).withDensity _
    have hp : Measurable (Function.uncurry (fun p y => w n (ρ p) y)) :=
      (hw n).comp (hρ.prodMap measurable_id)
    rw [ih, hmap, Measure.withDensity_compProd_withDensity
      (measurable_finiteHistoryDensity w hw n) hp]
    have hd := measurable_finiteHistoryDensity w hw (n+1)
    have hm := map_withDensity_pullback
      ((finiteHistoryLaw ν κ n) ⊗ₘ ((κ n).comap ρ hρ))
      (historySplit n).symm (historySplit n).symm.measurable
      (finiteHistoryDensity w (n+1)) hd
    convert! hm using 1
    congr 2
    funext p
    exact (finiteHistoryDensity_snoc w n p.1 p.2).symm

end FRSB
