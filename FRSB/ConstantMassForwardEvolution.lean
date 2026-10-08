module

public import FRSB.ForwardHeatDensity
public import FRSB.BackwardsConstantTime
public import FRSB.OptimalCurvatureMoment

@[expose] public section

/-! The actual Parisi h-transform of a genuine Gaussian heat density
satisfies the forward Fokker--Planck equation on every constant-CDF cell. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology
namespace FRSB
set_option maxHeartbeats 1000000

 def constantMassForwardDensity (β:ℝ) (μ:ParisiMeasure) (r m:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  Real.exp (m*parisiPotential β μ (t,x))*forwardHeatDensity β r F t x

 theorem hasDerivAt_constantMassForwardDensity_spatial (β:ℝ) (μ:ParisiMeasure)
    (r m:ℝ) (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) {t:ℝ} (ht:t∈Icc (0:ℝ) 1) (x:ℝ) :
    HasDerivAt (constantMassForwardDensity β μ r m F t)
      (Real.exp (m*parisiPotential β μ (t,x))*
        (deriv (forwardHeatDensity β r F t) x+
          m*parisiSpatialJet β μ 1 t x*forwardHeatDensity β r F t x)) x := by
  have hu:=(hasDerivAt_parisiPotential_spatial_all β μ t x ht).const_mul m |>.exp
  have hq:=hasDerivAt_forwardHeatDensity_spatial β r F hF K hK t x
  rw [←hq.deriv] at hq
  convert hu.mul hq using 1
  · rfl
  · rw [parisiSpatialJet_one]
    ring

 theorem iteratedDeriv_constantMassForwardDensity_two (β:ℝ) (μ:ParisiMeasure)
    (r m:ℝ) (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) {t:ℝ} (ht:t∈Icc (0:ℝ) 1) (x:ℝ) :
    iteratedDeriv 2 (constantMassForwardDensity β μ r m F t) x=
      Real.exp (m*parisiPotential β μ (t,x))*
        (iteratedDeriv 2 (forwardHeatDensity β r F t) x+
          2*m*parisiSpatialJet β μ 1 t x*deriv (forwardHeatDensity β r F t) x+
          (m*parisiSpatialJet β μ 2 t x+m^2*parisiSpatialJet β μ 1 t x^2)*
            forwardHeatDensity β r F t x) := by
  have hfirst:deriv (constantMassForwardDensity β μ r m F t)=fun y=>
      Real.exp (m*parisiPotential β μ (t,y))*(deriv (forwardHeatDensity β r F t) y+
        m*parisiSpatialJet β μ 1 t y*forwardHeatDensity β r F t y) :=
    funext fun y=>(hasDerivAt_constantMassForwardDensity_spatial β μ r m F hF K hK ht y).deriv
  have hu:=(hasDerivAt_parisiPotential_spatial_all β μ t x ht).const_mul m |>.exp
  have hB:=hasDerivAt_parisiSpatialJet_succ β μ 0 t x
  have hq:=hasDerivAt_forwardHeatDensity_spatial β r F hF K hK t x
  rw [←hq.deriv] at hq
  have hqq : HasDerivAt (deriv (forwardHeatDensity β r F t))
      (iteratedDeriv 2 (forwardHeatDensity β r F t) x) x := by
    have he:deriv (forwardHeatDensity β r F t)=forwardHeatDensityX β r F t :=
      funext fun y=>(hasDerivAt_forwardHeatDensity_spatial β r F hF K hK t y).deriv
    rw [he,iteratedDeriv_forwardHeatDensity_two β r F hF K hK]
    exact hasDerivAt_forwardHeatDensityX_spatial β r F hF K hK t x
  have hd:=hu.mul (hqq.add (((hB.const_mul m).mul hq)))
  have hdeq:=hd.deriv
  have hfun : ((fun y=>Real.exp (m*parisiPotential β μ (t,y)))*
      (deriv (forwardHeatDensity β r F t)+(fun y=>m*parisiSpatialJet β μ (0+1) t y)*
        forwardHeatDensity β r F t))=(fun y=>Real.exp (m*parisiPotential β μ (t,y))*
      (deriv (forwardHeatDensity β r F t) y+m*parisiSpatialJet β μ 1 t y*forwardHeatDensity β r F t y)) := rfl
  rw [hfun] at hdeq
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hfirst,hdeq]
  simp only [Pi.add_apply,Pi.mul_apply,Nat.reduceAdd]
  rw [parisiSpatialJet_one]
  ring

 theorem hasDerivAt_constantMassForwardDensity_time (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r:ℝ) (hr:0<r) {a b m:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1)
    (hc:∀s∈Ico a b,parisiCDF μ s=m) (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F)
    (K:ℕ→ℝ) (hK:∀j x,‖iteratedDeriv j F x‖≤K j) {t:ℝ}
    (ht:t∈Ioo a b) (hrt:r<t) (x:ℝ) :
    HasDerivAt (fun v=>constantMassForwardDensity β μ r m F v x)
      (β^2*((1/2:ℝ)*iteratedDeriv 2 (constantMassForwardDensity β μ r m F t) x-
        m*deriv (fun y=>parisiSpatialJet β μ 1 t y*constantMassForwardDensity β μ r m F t y) x)) t := by
  have ht01:t∈Icc (0:ℝ) 1:=⟨ha.trans ht.1.le,ht.2.le.trans hb⟩
  have hu:=(hasDerivAt_parisiPotential_constantCDF_time β hβ μ ha hab hb hc ht x).const_mul m |>.exp
  have hq:=hasDerivAt_forwardHeatDensity_time β r hβ hr F hF K hK hrt x
  have hp:=hasDerivAt_constantMassForwardDensity_spatial β μ r m F hF K hK ht01 x
  have hBp:= (hasDerivAt_parisiSpatialJet_succ β μ 0 t x).mul hp
  have hdBp : deriv (fun y=>parisiSpatialJet β μ 1 t y*constantMassForwardDensity β μ r m F t y) x=
      parisiSpatialJet β μ 2 t x*constantMassForwardDensity β μ r m F t x+
        parisiSpatialJet β μ 1 t x*(Real.exp (m*parisiPotential β μ (t,x))*
          (deriv (forwardHeatDensity β r F t) x+
            m*parisiSpatialJet β μ 1 t x*forwardHeatDensity β r F t x)) := by
    convert hBp.deriv using 1
  rw [hdBp,iteratedDeriv_constantMassForwardDensity_two β μ r m F hF K hK ht01 x]
  convert hu.mul hq using 1
  · rfl
  · unfold constantMassForwardDensity
    rw [parisiSpatialJet_one,parisiSpatialJet_two]
    ring

end FRSB
