module

public import FRSB.ConstantMassForwardEvolution
public import FRSB.ForwardActualHeatStep

@[expose] public section

/-! The actual optimal diffusion density satisfies the forward PDE on every
constant-CDF interval. Its time differentiation follows from the genuine
transition-law heat representation, including the correct endpoint-atom gauge. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

 def parisiForwardDensity (β:ℝ) (μ:ParisiMeasure) (t x:ℝ) : ℝ :=
  if ht:t∈Ioc (0:ℝ) 1 then forwardBridgeDensity β μ t ht x else 0

 theorem parisiForwardDensity_eq (β:ℝ) (μ:ParisiMeasure) {t:ℝ}
    (ht:t∈Ioc (0:ℝ) 1) :
    parisiForwardDensity β μ t=forwardBridgeDensity β μ t ht := by
  funext x
  simp only [parisiForwardDensity,dite_eq_left ht]

 theorem forwardEvolvedDensity_eq_constantMassForwardDensity (β:ℝ) (μ:ParisiMeasure)
    (r t:ℝ) (hr:r∈Ioc (0:ℝ) 1) (m:ℝ) :
    forwardEvolvedDensity β μ r t hr m=
      constantMassForwardDensity β μ r m (forwardBridgeFactor β μ r hr) t := by
  funext x
  simp only [forwardEvolvedDensity,constantMassForwardDensity,forwardHeatDensity,mul_assoc]

 theorem parisiForwardDensity_eq_constantMassForwardDensity (β:ℝ) (hβ:β≠0)
    (μ:ParisiMeasure) (r t:ℝ) (hr:r∈Ioc (0:ℝ) 1) (ht:t∈Ioc (0:ℝ) 1)
    (hrt:r<t) (m:ℝ) (hc:∀s∈Ico r t,parisiCDF μ s=m) :
    parisiForwardDensity β μ t=
      constantMassForwardDensity β μ r m (forwardBridgeFactor β μ r hr) t := by
  rw [parisiForwardDensity_eq β μ ht,forwardBridgeDensity_eq_evolved β hβ μ r t hr ht hrt m hc,
    forwardEvolvedDensity_eq_constantMassForwardDensity]

 theorem forwardBridgeFactor_uniform_derivative_bound (β:ℝ) (μ:ParisiMeasure)
    (r:ℝ) (hr:r∈Ioc (0:ℝ) 1) (j:ℕ) (x:ℝ) :
    ‖iteratedDeriv j (forwardBridgeFactor β μ r hr) x‖≤forwardBridgeExponentialConstant β j :=
  (forwardBridgeFactor_relative_derivative_bound β μ r hr j x).trans
    (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β j)
      (forwardBridgeFactor_le_one β μ r hr x))

 theorem hasDerivAt_parisiForwardDensity_time (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {a b m:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1)
    (hc:∀s∈Ico a b,parisiCDF μ s=m) {t:ℝ} (ht:t∈Ioo a b) (x:ℝ) :
    HasDerivAt (fun v=>parisiForwardDensity β μ v x)
      (β^2*((1/2:ℝ)*iteratedDeriv 2 (parisiForwardDensity β μ t) x-
        m*deriv (fun y=>parisiSpatialJet β μ 1 t y*parisiForwardDensity β μ t y) x)) t := by
  let r:ℝ:=(a+t)/2
  have hra:a<r :=by dsimp [r];linarith [ht.1]
  have hrt:r<t :=by dsimp [r];linarith [ht.1]
  have hr:r∈Ioc (0:ℝ) 1:=⟨ha.trans_lt hra,(hrt.trans (ht.2.trans_le hb)).le⟩
  let F:=forwardBridgeFactor β μ r hr
  let K:=forwardBridgeExponentialConstant β
  have hF:ContDiff ℝ ∞ F:=contDiff_forwardBridgeFactor β μ r hr
  have hK:∀j x,‖iteratedDeriv j F x‖≤K j:=forwardBridgeFactor_uniform_derivative_bound β μ r hr
  have hd:=hasDerivAt_constantMassForwardDensity_time β hβ μ r hr.1 ha hab hb hc F hF K hK ht hrt x
  have he:(fun v=>parisiForwardDensity β μ v x)=ᶠ[nhds t]
      (fun v=>constantMassForwardDensity β μ r m F v x) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t∈Ioo r b from ⟨hrt,ht.2⟩)] with v hv
    have hv01:v∈Ioc (0:ℝ) 1:=⟨hr.1.trans hv.1,hv.2.le.trans hb⟩
    exact congrFun (parisiForwardDensity_eq_constantMassForwardDensity β hβ μ r v hr hv01 hv.1 m
      (fun s hs=>hc s ⟨hra.le.trans hs.1,hs.2.trans hv.2⟩)) x
  have hp:parisiForwardDensity β μ t=constantMassForwardDensity β μ r m F t :=
    parisiForwardDensity_eq_constantMassForwardDensity β hβ μ r t hr
      ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩ hrt m
      (fun s hs=>hc s ⟨hra.le.trans hs.1,hs.2.trans ht.2⟩)
  have hh:=hd.congr_of_eventuallyEq he
  rwa [←hp] at hh

 theorem hasDerivAt_forwardBridgeDensity_time (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {a b m:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1)
    (hc:∀s∈Ico a b,parisiCDF μ s=m) {t:ℝ} (ht:t∈Ioo a b) (x:ℝ) :
    HasDerivAt (fun v=>parisiForwardDensity β μ v x)
      (β^2*((1/2:ℝ)*iteratedDeriv 2
        (forwardBridgeDensity β μ t ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩) x-
        m*deriv (fun y=>parisiSpatialJet β μ 1 t y*
          forwardBridgeDensity β μ t ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩ y) x)) t := by
  simpa only [parisiForwardDensity_eq β μ ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩] using
    hasDerivAt_parisiForwardDensity_time β hβ μ ha hab hb hc ht x

end FRSB
