module

public import FRSB.ForwardDensityPDE
public import FRSB.ConstantMassForwardRegularity

@[expose] public section

/-! Joint time-space continuity of the actual diffusion density and its
space/time PDE fields on each genuine constant-CDF interval. -/
noncomputable section
open Set Filter Paper
open scoped Topology ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

 def parisiForwardDensityT (β:ℝ) (μ:ParisiMeasure) (m t x:ℝ) : ℝ :=
  β^2*((1/2:ℝ)*iteratedDeriv 2 (parisiForwardDensity β μ t) x-
    m*(parisiSpatialJet β μ 2 t x*parisiForwardDensity β μ t x+
      parisiSpatialJet β μ 1 t x*deriv (parisiForwardDensity β μ t) x))

 theorem hasDerivAt_parisiForwardDensity_T (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {a b m:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1)
    (hc:∀s∈Ico a b,parisiCDF μ s=m) {t:ℝ} (ht:t∈Ioo a b) (x:ℝ) :
    HasDerivAt (fun v=>parisiForwardDensity β μ v x) (parisiForwardDensityT β μ m t x) t := by
  have ht01:t∈Ioc (0:ℝ) 1:=⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩
  have hp:HasDerivAt (parisiForwardDensity β μ t) (deriv (parisiForwardDensity β μ t) x) x := by
    rw [parisiForwardDensity_eq β μ ht01]
    exact ((contDiff_forwardBridgeDensity β μ t ht01).differentiable (by simp) x).hasDerivAt
  have hBp:=(hasDerivAt_parisiSpatialJet_succ β μ 0 t x).mul hp
  have hdBp:deriv (fun y=>parisiSpatialJet β μ 1 t y*parisiForwardDensity β μ t y) x=
      parisiSpatialJet β μ 2 t x*parisiForwardDensity β μ t x+
        parisiSpatialJet β μ 1 t x*deriv (parisiForwardDensity β μ t) x := by
    convert hBp.deriv using 1
  have hd:=hasDerivAt_parisiForwardDensity_time β hβ μ ha hab hb hc ht x
  rw [hdBp] at hd
  exact hd

 theorem continuousOn_parisiForwardDensity_fields (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {a b m:ℝ} (ha:0≤a) (_hab:a<b) (hb:b≤1) (hc:∀s∈Ico a b,parisiCDF μ s=m) :
    ContinuousOn (fun p:ℝ×ℝ=>parisiForwardDensity β μ p.1 p.2) (Ioo a b ×ˢ (univ:Set ℝ)) ∧
    ContinuousOn (fun p:ℝ×ℝ=>deriv (parisiForwardDensity β μ p.1) p.2) (Ioo a b ×ˢ (univ:Set ℝ)) ∧
    ContinuousOn (fun p:ℝ×ℝ=>iteratedDeriv 2 (parisiForwardDensity β μ p.1) p.2) (Ioo a b ×ˢ (univ:Set ℝ)) ∧
    ContinuousOn (fun p:ℝ×ℝ=>parisiForwardDensityT β μ m p.1 p.2) (Ioo a b ×ˢ (univ:Set ℝ)) := by
  let A0:ℝ×ℝ→ℝ:=fun p=>parisiForwardDensity β μ p.1 p.2
  let A1:ℝ×ℝ→ℝ:=fun p=>deriv (parisiForwardDensity β μ p.1) p.2
  let A2:ℝ×ℝ→ℝ:=fun p=>iteratedDeriv 2 (parisiForwardDensity β μ p.1) p.2
  let AT:ℝ×ℝ→ℝ:=fun p=>parisiForwardDensityT β μ m p.1 p.2
  have hlocal_cts:∀p∈Ioo a b ×ˢ (univ:Set ℝ),ContinuousAt A0 p∧ContinuousAt A1 p∧
      ContinuousAt A2 p∧ContinuousAt AT p := by
    intro p hp
    let r:ℝ:=(a+p.1)/2
    have hra:a<r:=by dsimp [r];linarith [hp.1.1]
    have hrt:r<p.1:=by dsimp [r];linarith [hp.1.1]
    have hr:r∈Ioc (0:ℝ) 1:=⟨ha.trans_lt hra,(hrt.trans (hp.1.2.trans_le hb)).le⟩
    let F:=forwardBridgeFactor β μ r hr
    let K:=forwardBridgeExponentialConstant β
    have hF:ContDiff ℝ ∞ F:=contDiff_forwardBridgeFactor β μ r hr
    have hK:∀j x,‖iteratedDeriv j F x‖≤K j:=forwardBridgeFactor_uniform_derivative_bound β μ r hr
    obtain ⟨hc0,hc1,hc2,hcT⟩:=continuousOn_constantMassForwardDensity_fields β r hβ hr.1 μ m F hF K hK
    have hlocal:∀z∈Ioo r b ×ˢ (univ:Set ℝ),
        A0 z=constantMassForwardDensity β μ r m F z.1 z.2∧
        A1 z=constantMassForwardDensityX β μ r m F z.1 z.2∧
        A2 z=constantMassForwardDensityXX β μ r m F z.1 z.2∧
        AT z=constantMassForwardDensityT β μ r m F z.1 z.2 := by
      intro z hz
      have hz01:z.1∈Ioc (0:ℝ) 1:=⟨hr.1.trans hz.1.1,hz.1.2.le.trans hb⟩
      have he:parisiForwardDensity β μ z.1=constantMassForwardDensity β μ r m F z.1:=
        parisiForwardDensity_eq_constantMassForwardDensity β hβ μ r z.1 hr hz01 hz.1.1 m
          (fun s hs=>hc s ⟨hra.le.trans hs.1,hs.2.trans hz.1.2⟩)
      have hX : A1 z=constantMassForwardDensityX β μ r m F z.1 z.2 := by
        change deriv (parisiForwardDensity β μ z.1) z.2=_
        rw [he]
        exact deriv_constantMassForwardDensity_eq_X β μ r m F hF K hK ⟨hz01.1.le,hz01.2⟩ z.2
      have hXX : A2 z=constantMassForwardDensityXX β μ r m F z.1 z.2 := by
        change iteratedDeriv 2 (parisiForwardDensity β μ z.1) z.2=_
        rw [he]
        exact iteratedDeriv_constantMassForwardDensity_eq_XX β μ r m F hF K hK ⟨hz01.1.le,hz01.2⟩ z.2
      refine ⟨congrFun he z.2,hX,hXX,?_⟩
      change β^2*((1/2:ℝ)*A2 z-m*(parisiSpatialJet β μ 2 z.1 z.2*A0 z+
        parisiSpatialJet β μ 1 z.1 z.2*A1 z))=_
      rw [hX,hXX,show A0 z=constantMassForwardDensity β μ r m F z.1 z.2 from congrFun he z.2]
      rfl
    have hN:Ioo r b ×ˢ (univ:Set ℝ)∈nhds p:=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hrt,hp.1.2⟩,mem_univ _⟩
    have hNc:Ioi r ×ˢ (univ:Set ℝ)∈nhds p:=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hrt,mem_univ _⟩
    have he0:A0=ᶠ[nhds p] fun z=>constantMassForwardDensity β μ r m F z.1 z.2 :=
      (show ∀ᶠz in nhds p,z∈Ioo r b ×ˢ (univ:Set ℝ) from hN).mono (fun z hz=>(hlocal z hz).1)
    have he1:A1=ᶠ[nhds p] fun z=>constantMassForwardDensityX β μ r m F z.1 z.2 :=
      (show ∀ᶠz in nhds p,z∈Ioo r b ×ˢ (univ:Set ℝ) from hN).mono (fun z hz=>(hlocal z hz).2.1)
    have he2:A2=ᶠ[nhds p] fun z=>constantMassForwardDensityXX β μ r m F z.1 z.2 :=
      (show ∀ᶠz in nhds p,z∈Ioo r b ×ˢ (univ:Set ℝ) from hN).mono (fun z hz=>(hlocal z hz).2.2.1)
    have heT:AT=ᶠ[nhds p] fun z=>constantMassForwardDensityT β μ r m F z.1 z.2 :=
      (show ∀ᶠz in nhds p,z∈Ioo r b ×ˢ (univ:Set ℝ) from hN).mono (fun z hz=>(hlocal z hz).2.2.2)
    exact ⟨(hc0.continuousAt hNc).congr he0.symm,(hc1.continuousAt hNc).congr he1.symm,
      (hc2.continuousAt hNc).congr he2.symm,(hcT.continuousAt hNc).congr heT.symm⟩
  exact ⟨continuousOn_of_forall_continuousAt (fun p hp=>(hlocal_cts p hp).1),
    continuousOn_of_forall_continuousAt (fun p hp=>(hlocal_cts p hp).2.1),
    continuousOn_of_forall_continuousAt (fun p hp=>(hlocal_cts p hp).2.2.1),
    continuousOn_of_forall_continuousAt (fun p hp=>(hlocal_cts p hp).2.2.2)⟩

end FRSB
