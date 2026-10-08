module

public import FRSB.ConstantMassLaw
public import FRSB.ForwardLeftAtoms
public import FRSB.ForwardTimeHeat
public import FRSB.BridgeDensityDisintegration
public import FRSB.ForwardDensityLaw
public import FRSB.ForwardHeatRegularity

@[expose] public section

/-! Tonelli's theorem turns an actual transition kernel and an actual
initial density into the density of the composed probability law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped Topology ENNReal NNReal
namespace FRSB

theorem kernel_comp_density {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (σ : Measure A) (ν : Measure B) [SFinite σ] [SFinite ν]
    (κ : Kernel A B) (ρ : A → ℝ≥0∞) (hρ : Measurable ρ)
    (k : A × B → ℝ≥0∞) (hk : Measurable k)
    (hκ : ∀ x, κ x = ν.withDensity (fun y => k (x,y))) :
    κ ∘ₘ σ.withDensity ρ =
      ν.withDensity (fun y => ∫⁻ x, ρ x * k (x,y) ∂σ) := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable,withDensity_apply _ hs]
  rw [lintegral_withDensity_eq_lintegral_mul _ hρ (κ.measurable_coe hs)]
  simp_rw [hκ,withDensity_apply _ hs]
  calc
    (∫⁻ x, ρ x * ∫⁻ y in s, k (x,y) ∂ν ∂σ) =
        ∫⁻ x, ∫⁻ y in s, ρ x * k (x,y) ∂ν ∂σ := by
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul _ (hk.comp measurable_prodMk_left)).symm
    _ = ∫⁻ y in s, ∫⁻ x, ρ x * k (x,y) ∂σ ∂ν :=
      lintegral_lintegral_swap ((hρ.comp measurable_fst).mul hk).aemeasurable

theorem integrable_gaussian_bridge_product {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (y : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (hFb : ∀ x, ‖F x‖ ≤ 1) :
    Integrable (fun x => heatDensity (t-r) (y-x) * heatDensity r x * F x) := by
  have hv : 0 < r*(t-r)/t := by have ht := hr.trans hrt; positivity
  have hg : Integrable (fun x => heatDensity (r*(t-r)/t) (x-r/t*y)) := by
    simpa only [heatDensity_sub_eq_gaussianPDFReal hv.le] using
      integrable_gaussianPDFReal (r/t*y) (r*(t-r)/t).toNNReal
  simp_rw [gaussian_bridge_density hr hrt y]
  exact (hg.const_mul (heatDensity t y)).mul_bdd hF.aestronglyMeasurable (.of_forall hFb)

theorem gaussian_bridge_lintegral_factor {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (y : ℝ) (F : ℝ → ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (hFb : ∀ x, ‖F x‖ ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (heatDensity (t-r) (y-x) * heatDensity r x * F x)) =
      ENNReal.ofReal (heatDensity t y * forwardHeatFactor r F t y) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussian_bridge_product hr hrt y F hF hFb)
    (.of_forall fun x => mul_nonneg (mul_nonneg (heatDensity_pos (sub_pos.mpr hrt) _).le
      (heatDensity_pos hr _).le) (hF0 x)),gaussian_bridge_convolution hr hrt y F hF]
  congr 2
  rw [forwardHeatFactor,forwardHeatVariance_eq r t (hr.trans hrt).ne']
  rfl

theorem parisiConstantMassKernel_apply_heat_density (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : 0 ≤ r) (hrt : r < t) (ht : t ≤ 1)
    (m : ℝ) (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) (x : ℝ) :
    parisiConstantMassKernel β μ r.toNNReal (t-r).toNNReal m x =
      volume.withDensity (fun y => ENNReal.ofReal (heatDensity (β^2*(t-r)) (y-x) *
        Real.exp (m*(parisiPotential β μ (t,y)-parisiPotential β μ (r,x))))) := by
  have hrn := Real.coe_toNNReal r hr
  have hdn := Real.coe_toNNReal (t-r) (sub_pos.mpr hrt).le
  have hsum : (r.toNNReal:ℝ)+(t-r).toNNReal=t := by rw [hrn,hdn]; ring
  have he := parisiConstantMassKernel_apply_actual β hβ μ r.toNNReal (t-r).toNNReal
    (Real.toNNReal_pos.mpr (sub_pos.mpr hrt)) (by rwa [hsum]) m
    (by simpa only [hrn,hdn,show r+(t-r)=t by ring] using hc) x
  rw [hsum,hrn,hdn] at he
  rw [he,gaussianReal_of_var_ne_zero _
    (Real.toNNReal_pos.mpr (mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hrt))).ne']
  rw [← withDensity_mul _ (measurable_gaussianPDF _ _) (by
    have hu : Continuous (fun y:ℝ => parisiPotential β μ (t,y)) := (continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)
    exact (Real.continuous_exp.comp ((hu.sub continuous_const).const_mul m)).measurable.ennreal_ofReal)]
  congr 1
  funext y
  change ENNReal.ofReal (gaussianPDFReal x (β^2*(t-r)).toNNReal y) * _ = _
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← heatDensity_sub_eq_gaussianPDFReal (mul_nonneg (sq_nonneg β) (sub_pos.mpr hrt).le)]

def forwardEvolvedDensity (β : ℝ) (μ : ParisiMeasure) (r t : ℝ)
    (hr : r ∈ Ioc (0 : ℝ) 1) (m x : ℝ) : ℝ :=
  Real.exp (m*parisiPotential β μ (t,x)) * heatDensity (β^2*t) x *
    forwardHeatFactor (β^2*r) (forwardBridgeFactor β μ r hr) (β^2*t) x

theorem parisiConstantMassKernel_comp_bridge_density (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hrt : r < t) (m : ℝ)
    (hc : ∀ s ∈ Ico r t, parisiCDF μ s = m) :
    parisiConstantMassKernel β μ r.toNNReal (t-r).toNNReal m ∘ₘ
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ r hr x)) =
      volume.withDensity (fun y => ENNReal.ofReal (forwardEvolvedDensity β μ r t hr m y)) := by
  let k : ℝ×ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (heatDensity (β^2*(t-r)) (p.2-p.1) * Real.exp
      (m*(parisiPotential β μ (t,p.2)-parisiPotential β μ (r,p.1))))
  have hu : Continuous (parisiPotential β μ) := continuous_parisiPotential β μ
  have hF : Continuous (forwardBridgeFactor β μ r hr) := (contDiff_forwardBridgeFactor β μ r hr).continuous
  have hk : Measurable k := by unfold k heatDensity; fun_prop
  rw [kernel_comp_density volume volume _ _
    (contDiff_forwardBridgeDensity β μ r hr).continuous.measurable.ennreal_ofReal k hk
    (parisiConstantMassKernel_apply_heat_density β hβ μ r t hr.1.le hrt ht.2 m hc)]
  congr 1
  funext y
  have hmr : parisiCDF μ r = m := hc r ⟨le_rfl,hrt⟩
  have he (x : ℝ) : ENNReal.ofReal (forwardBridgeDensity β μ r hr x) * k (x,y) =
      ENNReal.ofReal (Real.exp (m*parisiPotential β μ (t,y))) *
        ENNReal.ofReal (heatDensity (β^2*(t-r)) (y-x) * heatDensity (β^2*r) x *
          forwardBridgeFactor β μ r hr x) := by
    dsimp [k,forwardBridgeDensity]
    rw [hmr,← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg
      (heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) hr.1) _).le (Real.exp_pos _).le)
      (forwardBridgeFactor_pos β μ r hr _).le),← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    calc
      _ = (Real.exp (m*parisiPotential β μ (r,x)) *
          Real.exp (m*(parisiPotential β μ (t,y)-parisiPotential β μ (r,x)))) *
          (heatDensity (β^2*(t-r)) (y-x) * heatDensity (β^2*r) x * forwardBridgeFactor β μ r hr x) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by unfold heatDensity; fun_prop)]
  have htβ : β^2*r < β^2*t := mul_lt_mul_of_pos_left hrt (sq_pos_of_ne_zero hβ)
  rw [show β^2*(t-r)=β^2*t-β^2*r by ring,
    gaussian_bridge_lintegral_factor (mul_pos (sq_pos_of_ne_zero hβ) hr.1) htβ y
      (forwardBridgeFactor β μ r hr) (contDiff_forwardBridgeFactor β μ r hr).continuous.measurable
      (fun x => (forwardBridgeFactor_pos β μ r hr x).le)
      (fun x => by rw [Real.norm_of_nonneg (forwardBridgeFactor_pos β μ r hr x).le]; exact forwardBridgeFactor_le_one β μ r hr x),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  dsimp [forwardEvolvedDensity]
  ring

end FRSB
