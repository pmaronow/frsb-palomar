module

public import FRSB.ConstantMassForwardEvolution
public import FRSB.ForwardHeatDensityRegularity

@[expose] public section

/-! Jointly continuous representatives of the transformed density's space
jets and time PDE field, all identified with actual derivatives on a cell. -/
noncomputable section
open Set Filter Paper
open scoped Topology ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

 def constantMassForwardDensityX (β:ℝ) (μ:ParisiMeasure) (r m:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  Real.exp (m*parisiPotential β μ (t,x))*(forwardHeatDensityX β r F t x+
    m*parisiSpatialJet β μ 1 t x*forwardHeatDensity β r F t x)

 def constantMassForwardDensityXX (β:ℝ) (μ:ParisiMeasure) (r m:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  Real.exp (m*parisiPotential β μ (t,x))*(forwardHeatDensityXX β r F t x+
    2*m*parisiSpatialJet β μ 1 t x*forwardHeatDensityX β r F t x+
    (m*parisiSpatialJet β μ 2 t x+m^2*parisiSpatialJet β μ 1 t x^2)*forwardHeatDensity β r F t x)

 def constantMassForwardDensityT (β:ℝ) (μ:ParisiMeasure) (r m:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  β^2*((1/2:ℝ)*constantMassForwardDensityXX β μ r m F t x-
    m*(parisiSpatialJet β μ 2 t x*constantMassForwardDensity β μ r m F t x+
      parisiSpatialJet β μ 1 t x*constantMassForwardDensityX β μ r m F t x))

 theorem deriv_constantMassForwardDensity_eq_X (β:ℝ) (μ:ParisiMeasure) (r m:ℝ)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hK:∀j x,‖iteratedDeriv j F x‖≤K j)
    {t:ℝ} (ht:t∈Icc (0:ℝ) 1) (x:ℝ) :
    deriv (constantMassForwardDensity β μ r m F t) x=constantMassForwardDensityX β μ r m F t x := by
  rw [(hasDerivAt_constantMassForwardDensity_spatial β μ r m F hF K hK ht x).deriv,
    (hasDerivAt_forwardHeatDensity_spatial β r F hF K hK t x).deriv]
  rfl

 theorem iteratedDeriv_constantMassForwardDensity_eq_XX (β:ℝ) (μ:ParisiMeasure) (r m:ℝ)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hK:∀j x,‖iteratedDeriv j F x‖≤K j)
    {t:ℝ} (ht:t∈Icc (0:ℝ) 1) (x:ℝ) :
    iteratedDeriv 2 (constantMassForwardDensity β μ r m F t) x=constantMassForwardDensityXX β μ r m F t x := by
  rw [iteratedDeriv_constantMassForwardDensity_two β μ r m F hF K hK ht x,
    iteratedDeriv_forwardHeatDensity_two β r F hF K hK t x,
    (hasDerivAt_forwardHeatDensity_spatial β r F hF K hK t x).deriv]
  rfl

 theorem hasDerivAt_constantMassForwardDensity_T (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r:ℝ) (hr:0<r) {a b m:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1)
    (hc:∀s∈Ico a b,parisiCDF μ s=m) (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F)
    (K:ℕ→ℝ) (hK:∀j x,‖iteratedDeriv j F x‖≤K j) {t:ℝ}
    (ht:t∈Ioo a b) (hrt:r<t) (x:ℝ) :
    HasDerivAt (fun v=>constantMassForwardDensity β μ r m F v x)
      (constantMassForwardDensityT β μ r m F t x) t := by
  have ht01:t∈Icc (0:ℝ) 1:=⟨ha.trans ht.1.le,ht.2.le.trans hb⟩
  have hp:=hasDerivAt_constantMassForwardDensity_spatial β μ r m F hF K hK ht01 x
  have hBp:=(hasDerivAt_parisiSpatialJet_succ β μ 0 t x).mul hp
  have hdBp : deriv (fun y=>parisiSpatialJet β μ 1 t y*constantMassForwardDensity β μ r m F t y) x=
      parisiSpatialJet β μ 2 t x*constantMassForwardDensity β μ r m F t x+
        parisiSpatialJet β μ 1 t x*constantMassForwardDensityX β μ r m F t x := by
    rw [←deriv_constantMassForwardDensity_eq_X β μ r m F hF K hK ht01 x]
    rw [hp.deriv]
    convert hBp.deriv using 1
  have hd:=hasDerivAt_constantMassForwardDensity_time β hβ μ r hr ha hab hb hc F hF K hK ht hrt x
  rw [hdBp,iteratedDeriv_constantMassForwardDensity_eq_XX β μ r m F hF K hK ht01 x] at hd
  exact hd

 theorem continuousOn_constantMassForwardDensity_fields (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (μ:ParisiMeasure) (m:ℝ) (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) :
    ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensity β μ r m F p.1 p.2) (Ioi r ×ˢ (univ:Set ℝ)) ∧
    ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensityX β μ r m F p.1 p.2) (Ioi r ×ˢ (univ:Set ℝ)) ∧
    ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensityXX β μ r m F p.1 p.2) (Ioi r ×ˢ (univ:Set ℝ)) ∧
    ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensityT β μ r m F p.1 p.2) (Ioi r ×ˢ (univ:Set ℝ)) := by
  have he:ContinuousOn (fun p:ℝ×ℝ=>Real.exp (m*parisiPotential β μ (p.1,p.2)))
      (Ioi r ×ˢ (univ:Set ℝ)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_parisiPotential β μ))).continuousOn
  have hB:ContinuousOn (fun p:ℝ×ℝ=>parisiSpatialJet β μ 1 p.1 p.2) (Ioi r ×ˢ (univ:Set ℝ)):=
    (continuous_parisiSpatialJet_succ β μ 0).continuousOn
  have hC:ContinuousOn (fun p:ℝ×ℝ=>parisiSpatialJet β μ 2 p.1 p.2) (Ioi r ×ˢ (univ:Set ℝ)):=
    (continuous_parisiSpatialJet_succ β μ 1).continuousOn
  have hq:=continuousOn_forwardHeatDensity β r hβ hr F hF K hK
  have hqx:=continuousOn_forwardHeatDensityX β r hβ hr F hF K hK
  have hqxx:=continuousOn_forwardHeatDensityXX β r hβ hr F hF K hK
  have hp:ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensity β μ r m F p.1 p.2)
      (Ioi r ×ˢ (univ:Set ℝ)):=he.mul hq
  have hpx:ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensityX β μ r m F p.1 p.2)
      (Ioi r ×ˢ (univ:Set ℝ)):=he.mul (hqx.add ((continuousOn_const.mul hB).mul hq))
  have hpxx:ContinuousOn (fun p:ℝ×ℝ=>constantMassForwardDensityXX β μ r m F p.1 p.2)
      (Ioi r ×ˢ (univ:Set ℝ)):=he.mul ((hqxx.add ((continuousOn_const.mul hB).mul hqx)).add
        (((continuousOn_const.mul hC).add (continuousOn_const.mul (hB.pow 2))).mul hq))
  exact ⟨hp,hpx,hpxx,continuousOn_const.mul ((continuousOn_const.mul hpxx).sub
    (continuousOn_const.mul ((hC.mul hp).add (hB.mul hpx))))⟩

end FRSB
