module

public import FRSB.ForwardDensityComposition
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

@[expose] public section

/-! The genuine forward gauge evolves by the heat bridge across every
actual mass-free open interval. The terminal gauge removes the endpoint
atom, whereas the initial gauge retains its atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped Topology NNReal
namespace FRSB

theorem parisiLeftMass_eq_of_constantCDF (μ : ParisiMeasure) {r t m : ℝ}
    (hrt : r < t) (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) :
    parisiLeftMass μ t = m := by
  have hz := parisiMeasure_open_interval_eq_zero_of_cdf_constant μ hrt hc
  have he : {q : Overlap | (q:ℝ)<t} =
      {q : Overlap | (q:ℝ)≤r} ∪ {q : Overlap | (q:ℝ)∈Ioo r t} := by
    ext q
    simp only [mem_setOf_eq,mem_union,mem_Ioo]
    constructor
    · intro h
      exact (le_or_gt (q:ℝ) r).imp id (fun hr => ⟨hr,h⟩)
    · rintro (h | h)
      · exact h.trans_lt hrt
      · exact h.2
  have hd : Disjoint {q : Overlap | (q:ℝ)≤r} {q : Overlap | (q:ℝ)∈Ioo r t} := by
    apply disjoint_left.mpr
    intro q hq hi
    exact not_lt_of_ge hq hi.1
  have hm := hc r ⟨le_rfl,hrt⟩
  unfold parisiLeftMass
  rw [he,measure_union hd (measurableSet_Ioo.preimage measurable_subtype_coe),hz,add_zero]
  exact hm

theorem continuous_density_eq_of_withDensity_eq (p q : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (he : volume.withDensity (fun x => ENNReal.ofReal (p x)) =
      volume.withDensity (fun x => ENNReal.ofReal (q x))) : p = q := by
  apply Measure.eq_of_ae_eq (μ := volume) _ hp hq
  have ha := (withDensity_eq_iff_of_sigmaFinite
    hp.measurable.ennreal_ofReal.aemeasurable hq.measurable.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [ha] with x hx
  have hh := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (hp0 x),ENNReal.toReal_ofReal (hq0 x)] using hh

theorem continuous_forwardEvolvedDensity (β : ℝ) (μ : ParisiMeasure)
    (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) (m : ℝ) :
    Continuous (forwardEvolvedDensity β μ r t hr m) := by
  have hu : Continuous (fun x : ℝ => parisiPotential β μ (t,x)) :=
    (continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)
  have hF := contDiff_forwardBridgeFactor β μ r hr
  have hbound (j : ℕ) (x : ℝ) : ‖iteratedDeriv j (forwardBridgeFactor β μ r hr) x‖ ≤
      forwardBridgeExponentialConstant β j :=
    (forwardBridgeFactor_relative_derivative_bound β μ r hr j x).trans
      (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β j)
        (forwardBridgeFactor_le_one β μ r hr x))
  have hh := (contDiff_forwardHeatFactor (β^2*r) _ hF
    (forwardBridgeExponentialConstant β) hbound (β^2*t)).continuous
  unfold forwardEvolvedDensity heatDensity
  fun_prop

theorem forwardBridgeDensity_eq_evolved (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hrt : r < t) (m : ℝ)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) :
    forwardBridgeDensity β μ t ht = forwardEvolvedDensity β μ r t hr m := by
  have hsum : r.toNNReal+(t-r).toNNReal=t.toNNReal := by
    apply Subtype.ext
    change (r.toNNReal:ℝ)+(t-r).toNNReal=(t.toNNReal:ℝ)
    simp only [Real.coe_toNNReal _ hr.1.le,
      Real.coe_toNNReal _ (sub_pos.mpr hrt).le,Real.coe_toNNReal _ ht.1.le]
    ring
  have hc' : ∀ s ∈ Ico (r.toNNReal:ℝ) ((r.toNNReal:ℝ)+(t-r).toNNReal), parisiCDF μ s = m := by
    simpa only [Real.coe_toNNReal _ hr.1.le,Real.coe_toNNReal _ (sub_pos.mpr hrt).le,
      show r+(t-r)=t by ring] using hc
  have hsumR : (r.toNNReal:ℝ)+(t-r).toNNReal=t := by
    rw [← NNReal.coe_add,hsum,Real.coe_toNNReal _ ht.1.le]
  have he := selectedParisiState_constantMass_restricted_transitionLaw β 0 hβ μ
    r.toNNReal (t-r).toNNReal (Real.toNNReal_pos.mpr (sub_pos.mpr hrt))
    (by rw [hsumR]; exact ht.2) m hc' univ MeasurableSet.univ
  rw [Measure.restrict_univ,hsum,selectedState_endpoint_eq_bridgeDensity β hβ μ t ht,
    selectedState_endpoint_eq_bridgeDensity β hβ μ r hr,
    parisiConstantMassKernel_comp_bridge_density β hβ μ r t hr ht hrt m hc] at he
  apply continuous_density_eq_of_withDensity_eq _ _
    (contDiff_forwardBridgeDensity β μ t ht).continuous
    (continuous_forwardEvolvedDensity β μ r t hr m)
    (fun x => (forwardBridgeDensity_pos β hβ μ t ht x).le) _ he
  intro x
  have hbound (j : ℕ) (y : ℝ) : ‖iteratedDeriv j (forwardBridgeFactor β μ r hr) y‖ ≤
      forwardBridgeExponentialConstant β j :=
    (forwardBridgeFactor_relative_derivative_bound β μ r hr j y).trans
      (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β j)
        (forwardBridgeFactor_le_one β μ r hr y))
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) ht.1) _).le)
    (forwardHeatFactor_pos (β^2*r) _ (contDiff_forwardBridgeFactor β μ r hr)
      (forwardBridgeExponentialConstant β) hbound (forwardBridgeFactor_pos β μ r hr) _ _).le

theorem forwardBridgeLeftFactor_heat_step (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hrt : r < t) (m : ℝ)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) (x : ℝ) :
    forwardBridgeLeftFactor β μ t ht x =
      forwardHeatFactor (β^2*r) (forwardBridgeFactor β μ r hr) (β^2*t) x := by
  have he := congrFun (forwardBridgeDensity_eq_evolved β hβ μ r t hr ht hrt m hc) x
  have hm := parisiCDF_eq_left_add_atom μ t ht
  rw [parisiLeftMass_eq_of_constantCDF μ hrt hc] at hm
  dsimp [forwardBridgeDensity,forwardEvolvedDensity] at he
  rw [hm,add_mul,Real.exp_add] at he
  have hh : heatDensity (β^2*t) x * Real.exp (m*parisiPotential β μ (t,x)) *
      forwardBridgeLeftFactor β μ t ht x =
      heatDensity (β^2*t) x * Real.exp (m*parisiPotential β μ (t,x)) *
        forwardHeatFactor (β^2*r) (forwardBridgeFactor β μ r hr) (β^2*t) x := by
    dsimp [forwardBridgeLeftFactor]
    nlinarith [he]
  exact mul_left_cancel₀ (mul_ne_zero (heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) ht.1) x).ne'
    (Real.exp_pos _).ne') hh

theorem forwardBridgeLeftCorrection_heat_step (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hrt : r < t) (m : ℝ)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) :
    forwardBridgeLeftCorrection β μ t ht =
      forwardHeatCorrection (β^2*r) (β^2*t) (forwardBridgeCorrection β μ r hr) := by
  funext x
  rw [forwardBridgeLeftCorrection_eq_negativeLog,forwardBridgeLeftFactor_heat_step β hβ μ r t hr ht hrt m hc x]
  unfold forwardHeatCorrection forwardBridgeCorrection
  have he (y : ℝ) : Real.exp (- -Real.log (forwardBridgeFactor β μ r hr y)) =
      forwardBridgeFactor β μ r hr y := by
    rw [neg_neg,Real.exp_log (forwardBridgeFactor_pos β μ r hr y)]
  simp_rw [he]
  rw [forwardHeatFactor,forwardHeatVariance_eq _ _ (mul_pos (sq_pos_of_ne_zero hβ) ht.1).ne']
  rfl

end FRSB
