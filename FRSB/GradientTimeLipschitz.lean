module

public import FRSB.FiniteTimeHierarchy
public import FRSB.PolynomialMomentConvergence
public import FRSB.ClosedIntervalBounds
public import FRSB.GridMeasureIdentification
public import Paper.ParisiGradientMesh

@[expose] public section

/-! Uniform time Lipschitz regularity of the actual Parisi gradient, including
CDF jump times. This follows from finite-cell derivatives and actual uniform
finite-grid approximation, rather than a classical derivative at an atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FRSB
open SpinGlass.Targets
set_option maxHeartbeats 1000000

 def gradientTimeBound (β : ℝ) : ℝ := β^2/2*(uniformSpatialConstant β 2+
  2*uniformSpatialConstant β 0*uniformSpatialConstant β 1)

 theorem gradientTimeBound_nonneg (β : ℝ) : 0 ≤ gradientTimeBound β := by
  have h0 := (uniformSpatialConstant_pos β 0).le
  have h1 := (uniformSpatialConstant_pos β 1).le
  have h2 := (uniformSpatialConstant_pos β 2).le
  unfold gradientTimeBound
  positivity

 theorem norm_cellTimeForcing_one_le (β : ℝ) (μ : ParisiMeasure) (m : ℝ)
    (hm : m ∈ Icc (0 : ℝ) 1) (t x : ℝ) :
    ‖cellTimeForcing β μ m 1 t x‖ ≤ gradientTimeBound β := by
  have he : cellTimeForcing β μ m 1 t x=-(β^2/2)*
      (parisiSpatialJet β μ 3 t x+2*m*parisiSpatialJet β μ 1 t x*parisiSpatialJet β μ 2 t x) := by
    rw [cellTimeForcing_eq]
    norm_num [Finset.sum_range_succ] <;> ring_nf <;> simp
  have h0 := (norm_parisiSpatialJet_succ_le β μ 0 t x).trans
    (norm_spatialDerivativeBCF_le_uniform β μ 0)
  have h1 := (norm_parisiSpatialJet_succ_le β μ 1 t x).trans
    (norm_spatialDerivativeBCF_le_uniform β μ 1)
  have h2 := (norm_parisiSpatialJet_succ_le β μ 2 t x).trans
    (norm_spatialDerivativeBCF_le_uniform β μ 2)
  unfold gradientTimeBound
  rw [he,norm_mul,norm_neg,Real.norm_of_nonneg (by positivity : 0 ≤ β^2/2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_add_le _ _).trans
  apply add_le_add h2
  simp only [norm_mul,Real.norm_of_nonneg hm.1,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  have hm2 : (2 : ℝ)*m ≤ 2 := by linarith [hm.2]
  have hprod : 2*m*‖parisiSpatialJet β μ 1 t x‖ ≤ 2*uniformSpatialConstant β 0 :=
    mul_le_mul hm2 h0 (norm_nonneg _) (by norm_num)
  exact mul_le_mul hprod h1 (norm_nonneg _)
    (mul_nonneg (by norm_num) (uniformSpatialConstant_pos β 0).le)

 theorem finiteGradient_time_cell_bound (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) {l r : ℝ} (hl : s.q p ≤ l)
    (hlr : l ≤ r) (hr : r ≤ s.q (p+1)) (x : ℝ) :
    ‖parisiSpatialJet β (parisiSchemeMeasure s) 1 r x-
      parisiSpatialJet β (parisiSchemeMeasure s) 1 l x‖ ≤ gradientTimeBound β*(r-l) := by
  have hh := closed_interval_increment_bound
    (fun t => parisiSpatialJet β (parisiSchemeMeasure s) 1 t x) (fun _ => 0)
    (fun _ => gradientTimeBound β)
    ((continuous_parisiSpatialJet_succ β (parisiSchemeMeasure s) 0).comp
      (continuous_id.prodMk continuous_const))
    (fun _ _ => intervalIntegrable_const) (fun _ _ => intervalIntegrable_const) hq
    (by
      intro a b ha hab hb
      have hd (t : ℝ) (ht : t ∈ Icc a b) :=
        hasDerivAt_finiteCell_spatialJet_time s β hβ hp hq 1
          ⟨ha.trans_le ht.1,ht.2.trans_lt hb⟩ x
      have hm : s.m p ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩
      have hbnd := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t ht => (hd t ht).differentiableAt)
        (fun t ht => by rw [(hd t ht).deriv];exact norm_cellTimeForcing_one_le β _ _ hm t x)
        (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      simpa only [intervalIntegral.integral_zero,sub_zero,intervalIntegral.integral_const,
        smul_eq_mul,Real.norm_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hbnd)
    hl hlr hr
  simpa only [intervalIntegral.integral_zero,sub_zero,intervalIntegral.integral_const,
    smul_eq_mul,mul_comm] using hh

 theorem gridGradient_time_bound (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (n : ℕ)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hrt : r ≤ t) (x : ℝ) :
    ‖parisiSpatialJet β (parisiGridMeasure μ n) 1 t x-
      parisiSpatialJet β (parisiGridMeasure μ n) 1 r x‖ ≤ gradientTimeBound β*(t-r) := by
  let T := fun i => min t (max r (hjbGridTime n i))
  let F := fun i => parisiSpatialJet β (parisiGridMeasure μ n) 1 (T i) x
  have hgrid : Monotone (hjbGridTime n) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hTmono : Monotone T := (monotone_const.min (monotone_const.max hgrid))
  have htel := parisiGradientMesh_norm_telescope F (fun _ => gradientTimeBound β) T (n+1)
    (fun _ _ => intervalIntegrable_const) (by
      intro i hi
      by_cases he : T i=T (i+1)
      · simp only [F,he,sub_self,intervalIntegral.integral_same,norm_zero,le_refl]
      · have hlt : T i<T (i+1) := lt_of_le_of_ne (hTmono (Nat.le_succ i)) he
        have hir : r<hjbGridTime n (i+1) := by
          by_contra hh
          have hmax0 : max r (hjbGridTime n i)=r := max_eq_left
            ((hgrid (Nat.le_succ i)).trans (le_of_not_gt hh))
          have hmax1 : max r (hjbGridTime n (i+1))=r := max_eq_left (le_of_not_gt hh)
          exact he (by simp only [T,hmax0,hmax1])
        have hit : hjbGridTime n i<t := by
          by_contra hh
          have hmin0 : min t (max r (hjbGridTime n i))=t := min_eq_left
            ((le_of_not_gt hh).trans (le_max_right _ _))
          have hmin1 : min t (max r (hjbGridTime n (i+1)))=t := min_eq_left
            (((le_of_not_gt hh).trans (hgrid (Nat.le_succ i))).trans (le_max_right _ _))
          exact he (by simp only [T,hmin0,hmin1])
        have ha : hjbGridTime n i≤T i := le_min hit.le (le_max_right _ _)
        have hb : T (i+1)≤hjbGridTime n (i+1) := by
          dsimp only [T]
          rw [max_eq_right hir.le]
          exact min_le_right _ _
        let s := parisiGridRSBScheme μ n
        obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q μ n i hi
        have hq : s.q (i+1)<s.q (i+1+1) := by
          simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hjbGridTime_step_lt n i
        have hh := finiteGradient_time_cell_bound β hβ s (p:=i+1) (by omega) hq
          (by simpa only [s,hq0] using ha) hlt.le
          (by simpa only [s,show i+1+1=i+2 by omega,hq1] using hb) x
        rw [parisiSchemeMeasure_grid_eq μ n] at hh
        simpa only [F,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hh)
  have hg0 : hjbGridTime n 0=0 := by simp [hjbGridTime]
  have hg1 : hjbGridTime n (n+1)=1 := by
    unfold hjbGridTime
    exact div_self (by positivity)
  have h0 : T 0=r := by simp only [T,hg0,max_eq_left hr.1,min_eq_right hrt]
  have h1 : T (n+1)=t := by simp only [T,hg1,max_eq_right hr.2,min_eq_left ht.2]
  simpa only [F,h0,h1,intervalIntegral.integral_const,smul_eq_mul,mul_comm] using htel

 theorem parisiGradient_time_bound (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiGradient β μ (t,x)-parisiGradient β μ (r,x)‖ ≤ gradientTimeBound β*‖t-r‖ := by
  wlog hrt : r ≤ t generalizing r t
  · have hh := this ht hr (le_of_not_ge hrt)
    simpa only [norm_sub_rev] using hh
  have hF (u : ℝ) : Tendsto (fun n => parisiSpatialJet β (parisiGridMeasure μ n) 1 u x)
      atTop (nhds (parisiGradient β μ (u,x))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => ?_) (tendsto_parisiHJBGradientError β hβ μ)
    rw [parisiSpatialJet_one,parisiGradient_grid_eq_finite β hβ μ n,norm_sub_rev]
    exact parisiHJBGradientError_bound β μ n u x
  have hh := le_of_tendsto ((hF t).sub (hF r) |>.norm)
    (.of_forall fun n => gridGradient_time_bound β hβ μ n hr ht hrt x)
  simpa only [Real.norm_of_nonneg (sub_nonneg.mpr hrt)] using hh

end FRSB
