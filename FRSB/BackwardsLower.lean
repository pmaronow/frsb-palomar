module

public import FRSB.BackwardsFiniteLower

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB

theorem tendsto_backwardD_of_weak {A : Type*} {l : Filter A} (β : ℝ) (n : ℕ)
    (μ : Paper.ParisiMeasure) (ν : A → Paper.ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (p : ℝ × ℝ) :
    Tendsto (fun a => backwardD β (ν a) (n+1) p) l (𝓝 (backwardD β μ (n+1) p)) := by
  have he := (continuous_eval_const (F := Paper.ParisiSlabGradient 0 1)
    (projIcc 0 1 (by norm_num) p.1,p.2)).tendsto
    (Paper.bcfSpatialDerivative (Paper.parisiGradientBCF β μ) n)
  exact he.comp (tendsto_spatialDerivativeBCF_of_weak β n μ ν hν)

theorem tendsto_backwardQ_of_weak {A : Type*} {l : Filter A} (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (ν : A → Paper.ParisiMeasure) (hν : Tendsto ν l (𝓝 μ))
    (a t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => backwardQ β (ν n) a (t,x)) l (𝓝 (backwardQ β μ a (t,x))) := by
  have h2 := tendsto_backwardD_of_weak β 1 μ ν hν (t,x)
  have h3 := tendsto_backwardD_of_weak β 2 μ ν hν (t,x)
  have h4 := tendsto_backwardD_of_weak β 3 μ ν hν (t,x)
  have hc := (backwardC_pos β hβ μ t x ht).ne'
  exact ((h4.neg.div (tendsto_const_nhds.mul h2) (mul_ne_zero (by norm_num) hc)).add
    ((h3.pow 2).div (tendsto_const_nhds.mul (h2.pow 2))
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)))).sub (tendsto_const_nhds.mul h2)

/-- The lower Q bound for the actual solution of every probability measure,
including evaluation at its atoms. -/
theorem backwardQ_nonneg (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ backwardQ β μ (Paper.parisiCDF μ t) (t,x) := by
  let q : Paper.Overlap := ⟨t,ht⟩
  let S : Finset Paper.Overlap := {q}
  let ν := preservingMeasure μ S
  have hn : Tendsto (fun n => backwardQ β (ν n) (Paper.parisiCDF μ t) (t,x)) atTop
      (𝓝 (backwardQ β μ (Paper.parisiCDF μ t) (t,x))) :=
    tendsto_backwardQ_of_weak β hβ μ ν (tendsto_preservingMeasure μ S) _ t x ht
  apply ge_of_tendsto hn
  apply Eventually.of_forall
  intro n
  have he := finiteLaw_backwardQ_nonneg (ν n) (finite_support_preservingMeasure μ S n) β hβ t x ht
  have hm : Paper.parisiCDF (ν n) t = Paper.parisiCDF μ t :=
    preservingMeasure_cdf_mass μ S n q (by simp [S])
  simpa only [hm] using he

/-- The actual lower logarithmic-curvature bound z ≥ m B. -/
theorem backwardZ_ge_massB (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    Paper.parisiCDF μ t * backwardB β μ (t,x) ≤ backwardZ β μ (t,x) := by
  let a := Paper.parisiCDF μ t
  let f : ℝ → ℝ := fun y => backwardZ β μ (t,y) - a * backwardB β μ (t,y)
  have hd (y : ℝ) : HasDerivAt f (backwardQ β μ a (t,y)) y :=
    (hasDerivAt_backwardZ β hβ μ t y ht).sub ((hasDerivAt_backwardD β μ 1 t y ht).const_mul a)
  have hm : Monotone f := monotone_of_deriv_nonneg (fun y => (hd y).differentiableAt)
    (fun y => by rw [(hd y).deriv]; exact backwardQ_nonneg β hβ μ t y ht)
  have he := hm hx
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [backwardZ_at_zero β μ t ht,backwardB_at_zero β hβ μ t ht]
    ring
  rw [hf0] at he
  exact sub_nonneg.mp he

theorem backwardZ_nonneg (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 ≤ backwardZ β μ (t,x) :=
  (mul_nonneg (Paper.parisiCDF_nonneg μ t) (backwardB_nonneg β hβ μ t x ht hx)).trans
    (backwardZ_ge_massB β hβ μ t x ht hx)

/-- The actual sign of the third spatial derivative used by the forward PDE. -/
theorem backwardD_three_nonpos (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) : backwardD β μ 3 (t,x) ≤ 0 := by
  rw [backwardD_three_eq_neg_two_C_z β hβ μ t x ht]
  have hc := (backwardC_pos β hβ μ t x ht).le
  have hz := backwardZ_nonneg β hβ μ t x ht hx
  nlinarith

end FRSB
