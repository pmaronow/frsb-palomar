module

public import FRSB.ForwardLeftPotential

@[expose] public section

/-! Genuine spatial and variance derivatives of the Gaussian heat density. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

 theorem hasDerivAt_heatDensity_spatial (v x:ℝ) :
    HasDerivAt (heatDensity v) (-x/v*heatDensity v x) x := by
  have hd:=((((hasDerivAt_id x).pow 2).neg.div_const (2*v)).exp).const_mul
    ((Real.sqrt (2*Real.pi*v))⁻¹)
  convert hd using 1
  · rfl
  · simp only [heatDensity,Pi.neg_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    ring

 theorem hasDerivAt_deriv_heatDensity_spatial (v x:ℝ) :
    HasDerivAt (deriv (heatDensity v))
      ((x^2/v^2-1/v)*heatDensity v x) x := by
  have he:deriv (heatDensity v)=fun y=>-y/v*heatDensity v y :=
    funext fun y=>(hasDerivAt_heatDensity_spatial v y).deriv
  rw [he]
  have hd:=(((hasDerivAt_id x).neg.div_const v).mul (hasDerivAt_heatDensity_spatial v x))
  convert hd using 1
  · rfl
  · simp only [Pi.neg_apply,id_eq]
    ring

 theorem iteratedDeriv_heatDensity_two (v x:ℝ) :
    iteratedDeriv 2 (heatDensity v) x=(x^2/v^2-1/v)*heatDensity v x := by
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  exact (hasDerivAt_deriv_heatDensity_spatial v x).deriv

 theorem hasDerivAt_heatDensity_time (v x:ℝ) (hv:0<v) :
    HasDerivAt (fun w=>heatDensity w x)
      ((x^2/(2*v^2)-1/(2*v))*heatDensity v x) v := by
  have hs:Real.sqrt (2*Real.pi*v)≠0 :=ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hlog:HasDerivAt (fun w=>Real.log (Real.sqrt (2*Real.pi*w))) (1/(2*v)) v := by
    have hd:=(((hasDerivAt_id v).const_mul (2*Real.pi)).sqrt (by positivity)).log hs
    convert hd using 1
    · rfl
    · dsimp only [id_eq]
      have he:=Real.sq_sqrt (by positivity : 0≤2*Real.pi*v)
      field_simp [hs,hv.ne']
      have he' : Real.sqrt (2*v*Real.pi)^2=2*v*Real.pi:=Real.sq_sqrt (by positivity)
      nlinarith [he']
  have hd:=hlog.neg.sub ((hasDerivAt_const v (x^2)).div
    ((hasDerivAt_id v).const_mul 2) (by positivity : 2*v≠0))
  have hg:HasDerivAt (fun w=>Real.exp (-Real.log (Real.sqrt (2*Real.pi*w))-x^2/(2*w)))
      ((x^2/(2*v^2)-1/(2*v))*heatDensity v x) v := by
    convert hd.exp using 1
    · rfl
    · dsimp only [Pi.neg_apply,Pi.sub_apply,Pi.div_apply,id_eq]
      rw [show -Real.log (Real.sqrt (2*Real.pi*v))-x^2/(2*v)=
        -(Real.log (Real.sqrt (2*Real.pi*v))+x^2/(2*v)) by ring,
        ←negativeLog_heatDensity_eq v hv x,neg_neg,Real.exp_log (heatDensity_pos hv x)]
      field_simp [hv.ne']
      ring
  have he:(fun w=>heatDensity w x)=ᶠ[nhds v]
      (fun w=>Real.exp (-Real.log (Real.sqrt (2*Real.pi*w))-x^2/(2*w))) := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    rw [show -Real.log (Real.sqrt (2*Real.pi*w))-x^2/(2*w)=
      -(Real.log (Real.sqrt (2*Real.pi*w))+x^2/(2*w)) by ring,
      ←negativeLog_heatDensity_eq w hw x,neg_neg,Real.exp_log (heatDensity_pos hw x)]
  exact hg.congr_of_eventuallyEq he

 theorem hasDerivAt_heatDensity_time_pde (v x:ℝ) (hv:0<v) :
    HasDerivAt (fun w=>heatDensity w x) ((1/2:ℝ)*iteratedDeriv 2 (heatDensity v) x) v := by
  rw [iteratedDeriv_heatDensity_two]
  convert hasDerivAt_heatDensity_time v x hv using 1
  ring

end FRSB
