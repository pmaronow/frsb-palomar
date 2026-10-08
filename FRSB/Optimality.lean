module

public import FRSB.GammaPrime
public import FRSB.GammaEndpoints
public import Paper.ParisiJT
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! The actual Parisi optimality conditions, including the one-sided
curvature condition at zero. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

/-- A minimum at the right endpoint has nonpositive left derivative. -/
theorem derivative_nonpos_at_right_min (f : ℝ→ℝ) {a b d : ℝ} (hab:a<b)
    (hd:HasDerivAt f d b) (hmin:∀r∈Icc a b,f b≤f r) : d≤0 := by
  have ht := hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE b)
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT hab] with r hr
  rw [slope_fun_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmin r ⟨hr.1.le,hr.2.le⟩))
    (sub_nonpos.mpr hr.2.le)

/-- The necessary curvature condition at a right-accessible stationary
minimum. The argument also applies at the left endpoint. -/
theorem curvature_le_one_at_stationary_min
    (H K G : ℝ→ℝ) (hK:Continuous K)
    (hH:∀t,HasDerivAt H (K t) t) (c:ℝ) (hc:0<c)
    (hG:∀t,HasDerivAt G (c*(t-H t)) t)
    {q:ℝ} (hq:q<1) (hfixed:H q=q)
    (hmin:∀r∈Icc q 1,G q≤G r) : K q≤1 := by
  by_contra hbad
  have hk:1<K q := lt_of_not_ge hbad
  obtain ⟨l,u,⟨hl,hu⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hK.continuousAt.eventually (eventually_gt_nhds hk))
  let r:ℝ := min ((q+u)/2) ((q+1)/2)
  have hqr:q<r := lt_min (by linarith) (by linarith)
  have hru:r<u := (min_le_left _ _).trans_lt (by linarith)
  have hr1:r<1 := (min_le_right _ _).trans_lt (by linarith)
  have hkr:∀t∈Icc q r,1<K t := by
    intro t ht
    exact hsub ⟨hl.trans_le ht.1,ht.2.trans_lt hru⟩
  have hmono:StrictMonoOn (fun t=>H t-t) (Icc q r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc q r)
      ((fun t=>(hH t).continuousAt) |> continuous_iff_continuousAt.mpr |>.continuousOn |>.sub continuousOn_id)
    intro t ht
    rw [interior_Icc] at ht
    rw [((hH t).sub (hasDerivAt_id t)).deriv]
    linarith [hkr t ⟨ht.1.le,ht.2.le⟩]
  have hanti:StrictAntiOn G (Icc q r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc q r)
      ((continuous_iff_continuousAt.mpr fun t=>(hG t).continuousAt).continuousOn)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hG t).deriv]
    have hp:=hmono ⟨le_rfl,hqr.le⟩ ⟨ht.1.le,ht.2.le⟩ ht.1
    dsimp only at hp
    rw [hfixed,sub_self] at hp
    exact mul_neg_of_pos_of_neg hc (by linarith)
  have hh:=hanti ⟨le_rfl,hqr.le⟩ ⟨hqr.le,le_rfl⟩ hqr
  exact (not_lt_of_ge (hmin r ⟨hqr.le,hr1.le⟩)) hh

/-- A differentiable extension of physical Gamma, used solely to apply
ordinary interval calculus at the endpoints. -/
def gammaPrimitive (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure) (t:ℝ) : ℝ :=
  Gamma β μ 0+∫s in 0..t,gammaCurvatureSource β hβ μ μ s

theorem gammaPrimitive_eq (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : gammaPrimitive β hβ μ t=Gamma β μ t :=
  (Gamma_integral β hβ μ ht).symm

theorem hasDerivAt_gammaPrimitive (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure) (t:ℝ) :
    HasDerivAt (gammaPrimitive β hβ μ) (gammaCurvatureSource β hβ μ μ t) t := by
  have hc:=continuous_gammaCurvatureSource β hβ μ μ
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt).const_add _

def optimalityPotential (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure) (t:ℝ) : ℝ :=
  β^2/2*(∫s in t..1,gammaPrimitive β hβ μ s-s)

theorem hasDerivAt_optimalityPotential (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure) (t:ℝ) :
    HasDerivAt (optimalityPotential β hβ μ)
      (β^2/2*(t-gammaPrimitive β hβ μ t)) t := by
  have hc:Continuous (fun s=>gammaPrimitive β hβ μ s-s) :=
    (continuous_iff_continuousAt.mpr fun s=>(hasDerivAt_gammaPrimitive β hβ μ s).continuousAt).sub continuous_id
  convert (intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable t 1)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt).const_mul (β^2/2) using 1
  · rfl
  · ring

theorem optimalityPotential_eq_G (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {t:ℝ} (ht:t∈Icc (0:ℝ) 1) :
    optimalityPotential β hβ μ t=selectedParisiG β 0 hβ μ t := by
  unfold optimalityPotential selectedParisiG parisiG
  rw [intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.2] at hs
  dsimp only
  rw [gammaPrimitive_eq β hβ μ ⟨ht.1.trans hs.1,hs.2⟩,
    Gamma_eq_selectedSecondMoment β hβ μ]

/-- A support point of an actual minimizing measure is a minimum of the
physical G observable. -/
theorem optimalityPotential_min_of_support (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (hmin:∀ν:ParisiMeasure,parisiPDEFunctional β 0 μ≤parisiPDEFunctional β 0 ν)
    (q:Overlap) (hq:q∈(μ:Measure Overlap).support) :
    ∀r∈Icc (0:ℝ) 1,optimalityPotential β hβ μ q≤optimalityPotential β hβ μ r := by
  have hs:=(parisiJT_support_criterion β 0 hβ μ).mp hmin hq
  intro r hr
  rw [optimalityPotential_eq_G β hβ μ q.property,optimalityPotential_eq_G β hβ μ hr]
  exact hs ⟨r,hr⟩

/-- The terminal overlap is excluded from a minimizing measure's support. -/
theorem support_overlap_lt_one (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (hmin:∀ν:ParisiMeasure,parisiPDEFunctional β 0 μ≤parisiPDEFunctional β 0 ν)
    (q:Overlap) (hq:q∈(μ:Measure Overlap).support) : (q:ℝ)<1 := by
  by_contra hn
  have he:(q:ℝ)=1 := le_antisymm q.property.2 (le_of_not_gt hn)
  have hh:=derivative_nonpos_at_right_min (optimalityPotential β hβ μ) zero_lt_one
    (hasDerivAt_optimalityPotential β hβ μ 1) (by
      simpa only [he] using optimalityPotential_min_of_support β hβ μ hmin q hq)
  rw [gammaPrimitive_eq β hβ μ ⟨zero_le_one,le_rfl⟩] at hh
  have hp:0<β^2/2 := div_pos (sq_pos_of_ne_zero hβ) (by norm_num)
  exact not_le_of_gt (mul_pos hp (sub_pos.mpr (Gamma_terminal_lt_one β μ))) hh

/-- The self-consistency equation at every support point, including zero. -/
theorem Gamma_eq_overlap_of_support (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (hmin:∀ν:ParisiMeasure,parisiPDEFunctional β 0 μ≤parisiPDEFunctional β 0 ν)
    (q:Overlap) (hq:q∈(μ:Measure Overlap).support) : Gamma β μ q=(q:ℝ) := by
  by_cases hzero:(q:ℝ)=0
  · rw [hzero,Gamma_initial_zero β hβ μ]
  have hq0:0<(q:ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hzero)
  have hq1:=support_overlap_lt_one β hβ μ hmin q hq
  have hglobal:IsMinOn (optimalityPotential β hβ μ) (Icc (0:ℝ) 1) (q:ℝ) :=
    optimalityPotential_min_of_support β hβ μ hmin q hq
  have hlocal:IsLocalMin (optimalityPotential β hβ μ) (q:ℝ) :=
    hglobal.isLocalMin (Icc_mem_nhds hq0 hq1)
  have hh:=hlocal.hasDerivAt_eq_zero (hasDerivAt_optimalityPotential β hβ μ q)
  rw [gammaPrimitive_eq β hβ μ q.property] at hh
  have hp:(β^2/2:ℝ)≠0 := ne_of_gt (div_pos (sq_pos_of_ne_zero hβ) (by norm_num))
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hp)).symm

/-- The necessary curvature condition on the entire support, expressed by
the actual one-sided derivative rather than a derivative of a clamped curve. -/
theorem GammaPrime_le_one_of_support (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (hmin:∀ν:ParisiMeasure,parisiPDEFunctional β 0 μ≤parisiPDEFunctional β 0 ν)
    (q:Overlap) (hq:q∈(μ:Measure Overlap).support) : GammaPrime β μ q≤1 := by
  rw [GammaPrime_eq_source β hβ μ q.property]
  apply curvature_le_one_at_stationary_min (gammaPrimitive β hβ μ)
    (gammaCurvatureSource β hβ μ μ) (optimalityPotential β hβ μ)
    (continuous_gammaCurvatureSource β hβ μ μ)
    (hasDerivAt_gammaPrimitive β hβ μ) (β^2/2)
    (div_pos (sq_pos_of_ne_zero hβ) (by norm_num))
    (hasDerivAt_optimalityPotential β hβ μ)
    (support_overlap_lt_one β hβ μ hmin q hq)
  · rw [gammaPrimitive_eq β hβ μ q.property]
    exact Gamma_eq_overlap_of_support β hβ μ hmin q hq
  · intro r hr
    exact optimalityPotential_min_of_support β hβ μ hmin q hq r
      ⟨q.property.1.trans hr.1,hr.2⟩

end FRSB
