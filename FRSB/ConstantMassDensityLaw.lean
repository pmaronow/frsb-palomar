module

public import FRSB.ForwardDensityComposition
public import FRSB.ForwardActualHeatStep

@[expose] public section

/-! The actual constant-CDF density formula with an arbitrary initial law,
including the initial Dirac law at physical time zero. Tonelli is applied
at the measure level; no initial density is presumed. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal Topology
namespace FRSB
set_option maxHeartbeats 1000000

 theorem kernel_comp_measure_density {A B:Type*} [MeasurableSpace A] [MeasurableSpace B]
    (σ:Measure A) (ν:Measure B) [SFinite σ] [SFinite ν]
    (κ:Kernel A B) (k:A×B→ℝ≥0∞) (hk:Measurable k)
    (hκ:∀x,κ x=ν.withDensity (fun y=>k (x,y))) :
    κ ∘ₘ σ=ν.withDensity (fun y=>∫⁻x,k (x,y) ∂σ) := by
  simpa only [withDensity_one,Pi.one_apply,one_mul] using
    kernel_comp_density σ ν κ 1 measurable_const k hk hκ

 def constantMassDensityFromLaw (β:ℝ) (μ:ParisiMeasure) (r t m:ℝ)
    (ν:Measure ℝ) (x:ℝ) : ℝ :=
  Real.exp (m*parisiPotential β μ (t,x))*
    ∫y,heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y)) ∂ν

 theorem heatDensity_le_normalization {v:ℝ} (hv:0<v) (x:ℝ) :
    heatDensity v x≤(Real.sqrt (2*Real.pi*v))⁻¹ := by
  unfold heatDensity
  have he:Real.exp (-x^2/(2*v))≤1:=Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg x)) (by positivity))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity :(0:ℝ)≤(Real.sqrt (2*Real.pi*v))⁻¹)

 theorem constantMassDensity_integrand_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {r t m:ℝ} (_hr:0≤r) (hrt:r<t) (ht:t≤1) (hm:0 ≤ m) (x y:ℝ) :
    ‖heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y))‖≤
      (Real.sqrt (2*Real.pi*(β^2*(t-r))))⁻¹ := by
  have hv:0<β^2*(t-r):=mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.2 hrt)
  have hg:0≤heatDensity (β^2*(t-r)) (x-y):=(heatDensity_pos hv _).le
  have he:Real.exp (-m*parisiPotential β μ (r,y))≤1:=Real.exp_le_one_iff.2
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hm) (parisiPotential_nonneg β μ r y (hrt.le.trans ht)))
  rw [Real.norm_of_nonneg (mul_nonneg hg (Real.exp_pos _).le)]
  exact (mul_le_of_le_one_right hg he).trans (heatDensity_le_normalization hv _)

 theorem integrable_constantMassDensity_integrand (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {r t m:ℝ} (hr:0≤r) (hrt:r<t) (ht:t≤1) (hm:0 ≤ m)
    (ν:Measure ℝ) [IsFiniteMeasure ν] (x:ℝ) :
    Integrable (fun y=>heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y))) ν := by
  have hu:Continuous (fun y:ℝ=>parisiPotential β μ (r,y)):=by
    convert (continuous_parisiPotential β μ).comp
      (show Continuous (fun y:ℝ=>(r,y)) from continuous_const.prodMk continuous_id) using 1
    rfl
  apply (integrable_const ((Real.sqrt (2*Real.pi*(β^2*(t-r))))⁻¹)).mono' _
    (.of_forall fun y=>constantMassDensity_integrand_bound β hβ μ hr hrt ht hm x y)
  unfold heatDensity
  exact (by fun_prop : Continuous (fun y:ℝ=>(Real.sqrt (2*Real.pi*(β^2*(t-r))))⁻¹*
    Real.exp (-(x-y)^2/(2*(β^2*(t-r))))*Real.exp (-m*parisiPotential β μ (r,y)))).aestronglyMeasurable

 theorem constantMassDensityFromLaw_nonneg (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {r t m:ℝ} (_hr:0≤r) (hrt:r<t) (ν:Measure ℝ) (x:ℝ) :
    0≤constantMassDensityFromLaw β μ r t m ν x := by
  unfold constantMassDensityFromLaw
  exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun y=>mul_nonneg
    (heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.2 hrt)) _).le (Real.exp_pos _).le)

 theorem continuous_constantMassDensityFromLaw (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {r t m:ℝ} (hr:0≤r) (hrt:r<t) (ht:t≤1) (hm:0 ≤ m)
    (ν:Measure ℝ) [IsFiniteMeasure ν] : Continuous (constantMassDensityFromLaw β μ r t m ν) := by
  have hu:Continuous (fun y:ℝ=>parisiPotential β μ (r,y)):=by
    convert (continuous_parisiPotential β μ).comp
      (show Continuous (fun y:ℝ=>(r,y)) from continuous_const.prodMk continuous_id) using 1
    rfl
  have hf:Continuous (fun x:ℝ=>∫y,heatDensity (β^2*(t-r)) (x-y)*
      Real.exp (-m*parisiPotential β μ (r,y)) ∂ν):=by
    rw [continuous_iff_continuousAt]
    intro x
    apply tendsto_integral_filter_of_dominated_convergence
      (bound:=fun _=>((Real.sqrt (2*Real.pi*(β^2*(t-r))))⁻¹))
    · exact .of_forall fun z=>(integrable_constantMassDensity_integrand β hβ μ hr hrt ht hm ν z).aestronglyMeasurable
    · exact .of_forall fun z=>.of_forall fun y=>constantMassDensity_integrand_bound β hβ μ hr hrt ht hm z y
    · exact integrable_const _
    · exact .of_forall fun y=>by
        apply Continuous.tendsto
        unfold heatDensity
        fun_prop
  have huT:Continuous (fun x:ℝ=>parisiPotential β μ (t,x)):=by
    convert (continuous_parisiPotential β μ).comp
      (show Continuous (fun x:ℝ=>(t,x)) from continuous_const.prodMk continuous_id) using 1
    rfl
  exact (Real.continuous_exp.comp (continuous_const.mul huT)).mul hf

 theorem parisiConstantMassKernel_comp_initialLaw (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) (ν:Measure ℝ) [IsFiniteMeasure ν] :
    parisiConstantMassKernel β μ r.toNNReal (t-r).toNNReal m ∘ₘ ν=
      volume.withDensity (fun x=>ENNReal.ofReal (constantMassDensityFromLaw β μ r t m ν x)) := by
  let k:ℝ×ℝ→ℝ≥0∞:=fun p=>ENNReal.ofReal (heatDensity (β^2*(t-r)) (p.2-p.1)*
    Real.exp (m*(parisiPotential β μ (t,p.2)-parisiPotential β μ (r,p.1))))
  have hu := continuous_parisiPotential β μ
  have hk:Measurable k:=by unfold k heatDensity;fun_prop
  rw [kernel_comp_measure_density ν volume _ k hk
    (parisiConstantMassKernel_apply_heat_density β hβ μ r t hr hrt ht m hc)]
  congr 1
  funext x
  have hm:0 ≤ m:=by rw [←hc r ⟨le_rfl,hrt⟩];exact parisiCDF_nonneg μ r
  have he (y:ℝ):k (y,x)=ENNReal.ofReal (Real.exp (m*parisiPotential β μ (t,x)))*
      ENNReal.ofReal (heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y))) := by
    unfold k
    rw [←ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    dsimp only [Prod.fst,Prod.snd]
    rw [show m*(parisiPotential β μ (t,x)-parisiPotential β μ (r,y))=
      m*parisiPotential β μ (t,x)-m*parisiPotential β μ (r,y) by ring,
      Real.exp_sub,div_eq_mul_inv,neg_mul,Real.exp_neg]
    ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by unfold heatDensity;fun_prop),
    ←ofReal_integral_eq_lintegral_ofReal (integrable_constantMassDensity_integrand β hβ μ hr hrt ht hm ν x)
      (.of_forall fun y=>mul_nonneg
        (heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.2 hrt)) _).le (Real.exp_pos _).le),
    ←ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

 theorem selectedState_endpoint_eq_constantMassDensityLaw (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ t.toNNReal)=
      volume.withDensity (fun x=>ENNReal.ofReal (constantMassDensityFromLaw β μ r t m
        (canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)) x)) := by
  have htn:0≤t:=hr.trans hrt.le
  have hsum:r.toNNReal+(t-r).toNNReal=t.toNNReal:=by
    apply Subtype.ext
    change (r.toNNReal:ℝ)+(t-r).toNNReal=(t.toNNReal:ℝ)
    simp only [Real.coe_toNNReal _ hr,
      Real.coe_toNNReal _ (sub_pos.2 hrt).le,Real.coe_toNNReal _ htn]
    ring
  have hc':∀s∈Ico (r.toNNReal:ℝ) ((r.toNNReal:ℝ)+(t-r).toNNReal),parisiCDF μ s=m:=by
    simpa only [Real.coe_toNNReal _ hr,Real.coe_toNNReal _ (sub_pos.2 hrt).le,
      show r+(t-r)=t by ring] using hc
  have he:=selectedParisiState_constantMass_restricted_transitionLaw β 0 hβ μ r.toNNReal
    (t-r).toNNReal (Real.toNNReal_pos.2 (sub_pos.2 hrt))
    (by rw [Real.coe_toNNReal _ hr,Real.coe_toNNReal _ (sub_pos.2 hrt).le];linarith) m hc' univ MeasurableSet.univ
  rw [Measure.restrict_univ,hsum] at he
  rw [he,parisiConstantMassKernel_comp_initialLaw β hβ μ r t hr hrt ht m hc]

 theorem forwardBridgeDensity_eq_initialLaw_integral (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) :
    forwardBridgeDensity β μ t ⟨hr.trans_lt hrt,ht⟩=
      constantMassDensityFromLaw β μ r t m
        (canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)) := by
  let ν:=canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)
  let :IsProbabilityMeasure ν:=by dsimp only [ν];infer_instance
  have hm:0 ≤ m:=by rw [←hc r ⟨le_rfl,hrt⟩];exact parisiCDF_nonneg μ r
  apply continuous_density_eq_of_withDensity_eq _ _
    (contDiff_forwardBridgeDensity β μ t ⟨hr.trans_lt hrt,ht⟩).continuous
    (continuous_constantMassDensityFromLaw β hβ μ hr hrt ht hm ν)
    (fun x=>(forwardBridgeDensity_pos β hβ μ t ⟨hr.trans_lt hrt,ht⟩ x).le)
    (constantMassDensityFromLaw_nonneg β hβ μ hr hrt ν) _
  rw [←selectedState_endpoint_eq_bridgeDensity β hβ μ t ⟨hr.trans_lt hrt,ht⟩]
  exact selectedState_endpoint_eq_constantMassDensityLaw β hβ μ r t hr hrt ht m hc

 theorem integrable_constantMassDensity_initialLaw_integrand (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) (x:ℝ) :
    Integrable (fun y=>heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y)))
      (canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)) := by
  apply integrable_constantMassDensity_integrand β hβ μ hr hrt ht _ _ x
  rw [←hc r ⟨le_rfl,hrt⟩]
  exact parisiCDF_nonneg μ r

 theorem constantMassDensity_initialLaw_integral_pos (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) (x:ℝ) :
    0<∫y,heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y))
      ∂(canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)) := by
  have he:=congrFun (forwardBridgeDensity_eq_initialLaw_integral β hβ μ r t hr hrt ht m hc) x
  have hp:=forwardBridgeDensity_pos β hβ μ t ⟨hr.trans_lt hrt,ht⟩ x
  rw [he] at hp
  dsimp only [constantMassDensityFromLaw] at hp
  exact pos_of_mul_pos_right hp (Real.exp_pos _).le

/-- The literal real integral density display, with the genuine initial
 probability law even when the initial time is zero. -/
 theorem forwardBridgeDensity_constantMass_initialLaw_formula (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) (x:ℝ) :
    forwardBridgeDensity β μ t ⟨hr.trans_lt hrt,ht⟩ x=
      Real.exp (m*parisiPotential β μ (t,x))*
        ∫y,heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y))
          ∂(canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)) :=
  congrFun (forwardBridgeDensity_eq_initialLaw_integral β hβ μ r t hr hrt ht m hc) x

 theorem selectedState_initialLaw_zero (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ 0)=Measure.dirac 0 := by
  have he:selectedParisiItoState β 0 hβ μ 0=fun _=>0:=by
    funext sample
    exact canonicalParisiItoState_zero β 0 μ _ _ _ _ sample
  rw [he,Measure.map_const]
  simp

 theorem forwardBridgeDensity_constantMass_from_zero (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {t:ℝ} (ht:0<t) (ht1:t≤1) (m:ℝ) (hc:∀s∈Ico (0:ℝ) t,parisiCDF μ s=m)
    (x:ℝ) : forwardBridgeDensity β μ t ⟨ht,ht1⟩ x=
      heatDensity (β^2*t) x*Real.exp (m*(parisiPotential β μ (t,x)-parisiPotential β μ (0,0))) := by
  rw [forwardBridgeDensity_constantMass_initialLaw_formula β hβ μ 0 t (le_refl 0) ht ht1 m hc x]
  rw [Real.toNNReal_zero,selectedState_initialLaw_zero]
  simp only [sub_zero,integral_dirac]
  rw [show m*(parisiPotential β μ (t,x)-parisiPotential β μ (0,0))=
    m*parisiPotential β μ (t,x)+(-m*parisiPotential β μ (0,0)) by ring,Real.exp_add]
  ring

end FRSB
