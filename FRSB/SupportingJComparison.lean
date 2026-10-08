module

public import FRSB.SupportingJCalculus
public import FRSB.MeasureCellInduction
public import FRSB.BackwardsRelativeActual

@[expose] public section

/-! Closed-cell comparison for the literal norm barrier, including repeated
finite overlap nodes. This independently instantiates the displayed norm proof. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem supportingJConstant_ge_one (β : ℝ) : 1 ≤ supportingJConstant β := by
  have hh := uniformSpatialConstant_pos β 2
  unfold supportingJConstant
  linarith

def supportingJNormBound (β : ℝ) : ℝ := uniformSpatialConstant β 1+
  uniformSpatialConstant β 2+uniformSpatialConstant β 3+uniformSpatialConstant β 4

theorem supportingJNormBound_pos (β : ℝ) : 0 < supportingJNormBound β := by
  have h1 := uniformSpatialConstant_pos β 1
  have h2 := uniformSpatialConstant_pos β 2
  have h3 := uniformSpatialConstant_pos β 3
  have h4 := uniformSpatialConstant_pos β 4
  unfold supportingJNormBound
  positivity

theorem backwardTauJ_le_uniform (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) :
    backwardTauJ β μ q ≤ supportingJNormBound β := by
  have hh := jetNorm4_le_abs_sum (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
    (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
  have h1 := backwardTauD_uniform_bound β μ 1 q
  have h2 := backwardTauD_uniform_bound β μ 2 q
  have h3 := backwardTauD_uniform_bound β μ 3 q
  have h4 := backwardTauD_uniform_bound β μ 4 q
  dsimp only [backwardTauJ,supportingJNormBound]
  linarith

theorem finiteCell_classical_J {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauJ β (Paper.parisiSchemeMeasure s)) := by
  refine ⟨(continuous_backwardTauJ β _).continuousOn,?_,?_,?_,?_⟩
  · refine ⟨supportingJNormBound β,(supportingJNormBound_pos β).le,fun t _ x => ?_⟩
    have hJn : 0 ≤ backwardTauJ β (Paper.parisiSchemeMeasure s) (t,x) := jetNorm4_nonneg _ _ _ _
    rw [abs_of_nonneg hJn]
    exact backwardTauJ_le_uniform β _ _
  · exact fun t ht x => (hasDerivAt_finiteCell_backwardTauJ s β hβ hp ht x).differentiableAt
  · exact fun t ht x => (hasDerivAt_backwardTauJ_spatial β hβ _ t x
      (backwardCell_mem_global s β hp ht)).differentiableAt
  · intro t ht x
    have hg := backwardCell_mem_global s β hp ht
    have heq : deriv (fun y => backwardTauJ β (Paper.parisiSchemeMeasure s) (t,y)) =
        fun y => backwardTauJx β (Paper.parisiSchemeMeasure s) (t,y) :=
      funext fun y => (hasDerivAt_backwardTauJ_spatial β hβ _ t y hg).deriv
    rw [heq]
    exact (hasDerivAt_backwardTauJx_spatial β hβ _ t x hg).differentiableAt

theorem continuous_backwardJBarrier (β : ℝ) (μ : Paper.ParisiMeasure) :
    Continuous (backwardJBarrier β μ) := by
  unfold backwardJBarrier
  exact (((Real.continuous_exp.comp (continuous_fst.const_mul (supportingJConstant β))).const_mul 10).mul
    (continuous_backwardTauD β μ 2)).sub (continuous_backwardTauJ β μ)

theorem backwardJBarrier_abs_le (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ) :
    |backwardJBarrier β μ (τ,x)| ≤
      10*Real.exp (supportingJConstant β*β^2)+supportingJNormBound β := by
  have hC := backwardTauC_pos_le_one β hβ μ τ x hτ
  have hJ := backwardTauJ_le_uniform β μ (τ,x)
  have hexp : Real.exp (supportingJConstant β*τ) ≤
      Real.exp (supportingJConstant β*β^2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ.2 (supportingJConstant_pos β).le)
  have hprod := mul_le_mul_of_nonneg_left hC.2
    (by positivity : 0 ≤ 10*Real.exp (supportingJConstant β*τ))
  have hh := norm_sub_le (10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 2 (τ,x))
    (backwardTauJ β μ (τ,x))
  have hp : 0 ≤ 10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 2 (τ,x) :=
    mul_nonneg (by positivity) hC.1.le
  have hJn : 0 ≤ backwardTauJ β μ (τ,x) := jetNorm4_nonneg _ _ _ _
  simp only [Real.norm_eq_abs,abs_of_nonneg hp,abs_of_nonneg hJn] at hh
  dsimp only [backwardJBarrier]
  nlinarith

theorem finiteCell_classical_JBarrier {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardJBarrier β (Paper.parisiSchemeMeasure s)) := by
  refine ⟨(continuous_backwardJBarrier β _).continuousOn,?_,?_,?_,?_⟩
  · refine ⟨10*Real.exp (supportingJConstant β*β^2)+supportingJNormBound β,?_,fun t ht x => ?_⟩
    · have hh := (supportingJNormBound_pos β).le
      positivity
    · exact backwardJBarrier_abs_le β hβ _ (backwardCell_mem_global s β hp ht) x
  · exact fun t ht x => (hasDerivAt_finiteCell_backwardJBarrier s β hβ hp ht x).differentiableAt
  · exact fun t ht x => (hasDerivAt_backwardJBarrier_spatial β hβ _ t x
      (backwardCell_mem_global s β hp ht)).differentiableAt
  · intro t ht x
    have hg := backwardCell_mem_global s β hp ht
    have heq : deriv (fun y => backwardJBarrier β (Paper.parisiSchemeMeasure s) (t,y)) =
        fun y => 10*Real.exp (supportingJConstant β*t)*backwardTauD β (Paper.parisiSchemeMeasure s) 3 (t,y)-
          backwardTauJx β (Paper.parisiSchemeMeasure s) (t,y) :=
      funext fun y => (hasDerivAt_backwardJBarrier_spatial β hβ _ t y hg).deriv
    rw [heq]
    exact (((hasDerivAt_backwardTauD_spatial β hβ _ 3 t x hg).const_mul
      (10*Real.exp (supportingJConstant β*t))).sub
      (hasDerivAt_backwardTauJx_spatial β hβ _ t x hg)).differentiableAt

/-- Genuine comparison propagates the displayed barrier through a closed cell. -/
theorem finiteCell_JBarrier_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hinit : ∀ x, 0 ≤ backwardJBarrier β (Paper.parisiSchemeMeasure s) (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      0 ≤ backwardJBarrier β (Paper.parisiSchemeMeasure s) (τ,x) := by
  have hq := s.q_mono p hp
  have hac : backwardCellStart s β p ≤ backwardCellEnd s β p := by
    unfold backwardCellStart backwardCellEnd
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hq _) (sq_nonneg β)
  have hv := finiteCell_classical_JBarrier s β hβ hp
  have hh := hv.supersolution_nonneg hac false
    (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
    (fun _ => supportingJConstant β) (supportingJConstant β) (supportingJConstant_pos β).le
    (fun t ht x _ => by
      have h := backwardTau_drift_outward β hβ (Paper.parisiSchemeMeasure s) (s.m p) t x
        ⟨s.m_nonneg hp,s.m_le_one hp⟩ (backwardCell_mem_global s β hp ⟨ht.1.le,ht.2.le⟩)
      exact h.trans (supportingJConstant_ge_one β))
    (fun _ _ _ _ => le_rfl)
    (fun t ht x _ => finiteCell_JBarrier_supersolution s β hβ hp ht x)
    (fun x _ => hinit x)
    (by intro h; contradiction)
  exact fun t ht x => hh t ht x (mem_univ x)

/-- The literal J barrier is nonnegative across all actual finite overlap cells. -/
theorem finiteScheme_JBarrier_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ τ ∈ Icc 0 (β^2), ∀ x, 0 ≤ backwardJBarrier β (Paper.parisiSchemeMeasure s) (τ,x) := by
  apply backward_scheme_cell_induction s β
    (fun τ => ∀ x, 0 ≤ backwardJBarrier β (Paper.parisiSchemeMeasure s) (τ,x))
  · exact backwardJBarrier_initial_nonneg β _
  · intro p hp hinit
    exact finiteCell_JBarrier_nonneg s β hβ hp hinit

theorem finiteScheme_J_relative_factor {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ) :
    backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x) ≤
      10*Real.exp (supportingJConstant β*τ)*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  have hh := finiteScheme_JBarrier_nonneg s β hβ τ hτ x
  exact sub_nonneg.mp hh

theorem tendsto_backwardTauJ_of_weak {ι : Type*} {L : Filter ι} (β : ℝ)
    (μ : Paper.ParisiMeasure) (ν : ι → Paper.ParisiMeasure)
    (hν : Tendsto ν L (𝓝 μ)) (q : ℝ × ℝ) :
    Tendsto (fun i => backwardTauJ β (ν i) q) L (𝓝 (backwardTauJ β μ q)) := by
  have h2 := tendsto_backwardD_of_weak β 1 μ ν hν (backwardTime β q.1,q.2)
  have h3 := tendsto_backwardD_of_weak β 2 μ ν hν (backwardTime β q.1,q.2)
  have h4 := tendsto_backwardD_of_weak β 3 μ ν hν (backwardTime β q.1,q.2)
  have h5 := tendsto_backwardD_of_weak β 4 μ ν hν (backwardTime β q.1,q.2)
  have hs := (((h2.pow 2).add (h3.pow 2)).add (h4.pow 2)).add (h5.pow 2)
  exact (Real.continuous_sqrt.tendsto _).comp hs

/-- The same norm barrier holds for every actual probability-measure solution,
by the genuine weak finite-measure approximation. -/
theorem backwardTauJ_relative_factor (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ) :
    backwardTauJ β μ (τ,x) ≤
      10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 2 (τ,x) := by
  let ν := preservingMeasure μ ∅
  have hν := tendsto_preservingMeasure μ ∅
  have hJ := tendsto_backwardTauJ_of_weak β μ ν hν (τ,x)
  have hC : Tendsto (fun n => 10*Real.exp (supportingJConstant β*τ)*backwardTauD β (ν n) 2 (τ,x))
      atTop (𝓝 (10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 2 (τ,x))) :=
    tendsto_const_nhds.mul (tendsto_backwardD_of_weak β 1 μ ν hν (backwardTime β τ,x))
  apply le_of_tendsto_of_tendsto hJ hC
  apply Eventually.of_forall
  intro n
  have hh := finiteScheme_J_relative_factor (preservingRSBScheme μ ∅ n) β hβ hτ x
  simpa only [parisiSchemeMeasure_preservingRSBScheme] using hh

/-- The uniform relative constant obtained by the literal norm proof. -/
def supportingJRelativeConstant (β : ℝ) : ℝ := 10*Real.exp (supportingJConstant β*β^2)

theorem supportingJRelativeConstant_pos (β : ℝ) : 0 < supportingJRelativeConstant β := by
  unfold supportingJRelativeConstant
  positivity

theorem backwardTauJ_relative_bound (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ) :
    backwardTauJ β μ (τ,x) ≤ supportingJRelativeConstant β*backwardTauD β μ 2 (τ,x) := by
  have hh := backwardTauJ_relative_factor β hβ μ hτ x
  have hexp := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hτ.2 (supportingJConstant_pos β).le)
  have hmul := mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ) ≤ 10)
  exact hh.trans (mul_le_mul_of_nonneg_right hmul (backwardTauC_pos_le_one β hβ μ τ x hτ).1.le)

/-- Each component is bounded by the same norm-derived relative constant. -/
theorem backwardTauD_relative_bound_via_J (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ)
    (j : ℕ) (hj : j ∈ Finset.Icc 2 5) :
    |backwardTauD β μ j (τ,x)| ≤ supportingJRelativeConstant β*backwardTauD β μ 2 (τ,x) := by
  obtain ⟨h2,h3,h4,h5⟩ := jetNorm4_abs_component_le (backwardTauD β μ 2 (τ,x))
    (backwardTauD β μ 3 (τ,x)) (backwardTauD β μ 4 (τ,x)) (backwardTauD β μ 5 (τ,x))
  have hh := backwardTauJ_relative_bound β hβ μ hτ x
  rcases Finset.mem_Icc.mp hj with ⟨hj0,hj1⟩
  interval_cases j
  · exact h2.trans hh
  · exact h3.trans hh
  · exact h4.trans hh
  · exact h5.trans hh

end FRSB
