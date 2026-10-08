module

public import FRSB.PolynomialMomentIdentity
public import FRSB.MomentConstantBootstrap
public import FRSB.GammaSecond

@[expose] public section

/-! Genuine differentiation and simultaneous smoothness of the actual
polynomial moments. Endpoint coefficients are taken from the continuous
one-sided representative, so a terminal atom does not alter left derivatives. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

 theorem hasDerivAt_moment_of_continuousAt_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (f:MomentPolynomial) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1)
    (hCDF:ContinuousAt (parisiCDF μ) t) :
    HasDerivAt (moment β μ f)
      (β^2*(moment β μ (momentDrift0 f) t+parisiCDF μ t*moment β μ (momentDrift1 f) t)) t := by
  have hc:ContinuousAt (polynomialMomentSource β hβ μ μ f) t :=
    continuousAt_const.mul (((continuous_fixedStatePolynomialMoment β hβ μ μ _).continuousAt).add
      (hCDF.mul (continuous_fixedStatePolynomialMoment β hβ μ μ _).continuousAt))
  have hd:=(intervalIntegral.integral_hasDerivAt_right
    (polynomialMomentSource_intervalIntegrable β hβ μ μ f 0 t)
    (polynomialMomentSource_measurable β hβ μ μ f).aestronglyMeasurable.stronglyMeasurableAtFilter hc).const_add
      (moment β μ f 0)
  have he:moment β μ f =ᶠ[nhds t] fun r=>moment β μ f 0+
      ∫s in 0..r,polynomialMomentSource β hβ μ μ f s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact moment_integral β hβ μ f ⟨hr.1.le,hr.2.le⟩
  rw [polynomialMomentSource_self_physical β hβ μ f ⟨ht.1.le,ht.2.le⟩] at hd
  exact hd.congr_of_eventuallyEq he

 theorem hasDerivAt_moment_of_constant_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) (f:MomentPolynomial)
    {t:ℝ} (ht:t∈Ioo a b) : HasDerivAt (moment β μ f)
      (β^2*(moment β μ (momentDrift0 f) t+m*moment β μ (momentDrift1 f) t)) t := by
  have hh:=hasDerivAt_moment_of_continuousAt_CDF β hβ μ f (hI ht)
    (continuousAt_CDF_of_constant_on_Ioo μ m a b hCDF ht)
  rwa [hCDF t ht] at hh

 theorem contDiffOn_moment_of_constant_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) (f:MomentPolynomial) :
    ContDiffOn ℝ ∞ (moment β μ f) (Ioo a b) := by
  apply moments_contDiffOn_constant_hierarchy (moment β μ) momentDrift0 momentDrift1 β m a b
  · intro g
    exact (continuousOn_moment β hβ μ g).mono (fun t ht=>⟨(hI ht).1.le,(hI ht).2.le⟩)
  · intro g t ht
    exact hasDerivAt_moment_of_constant_CDF β hβ μ m a b hI hCDF g ht

 theorem hasDerivWithinAt_moment_of_continuous_coefficient (β:ℝ) (hβ:β≠0)
    (μ:ParisiMeasure) (q:ℝ) (hq:0≤q) (hq1:q≤1) (c:ℝ→ℝ)
    (hc:ContinuousOn c (Icc (0:ℝ) q))
    (hcoeff:∀s∈Ioo (0:ℝ) q,parisiCDF μ s=c s)
    (f:MomentPolynomial) {t:ℝ} (ht:t∈Icc (0:ℝ) q) :
    HasDerivWithinAt (moment β μ f)
      (β^2*(moment β μ (momentDrift0 f) t+c t*moment β μ (momentDrift1 f) t))
      (Icc (0:ℝ) q) t := by
  have hsub:Icc (0:ℝ) q⊆Icc (0:ℝ) 1:=Icc_subset_Icc le_rfl hq1
  have he:∀u∈Icc (0:ℝ) q,moment β μ f u=moment β μ f 0+
      ∫s in 0..u,β^2*(moment β μ (momentDrift0 f) s+c s*moment β μ (momentDrift1 f) s) := by
    intro u hu
    have hh:=moment_interval_integral_physical β hβ μ f ⟨le_rfl,hq.trans hq1⟩ (hsub hu)
    have hi:(β^2*∫s in 0..u,moment β μ (momentDrift0 f) s+
        parisiCDF μ s*moment β μ (momentDrift1 f) s)=
      ∫s in 0..u,β^2*(moment β μ (momentDrift0 f) s+c s*moment β μ (momentDrift1 f) s) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le hu.1
      intro s hs
      dsimp only
      rw [hcoeff s ⟨hs.1,hs.2.trans_le hu.2⟩]
    rw [hi] at hh
    linarith
  apply hasDerivWithinAt_of_interval_identity _ _ q _ he t ht
  exact continuousOn_const.mul (((continuousOn_moment β hβ μ _).mono hsub).add
    (hc.mul ((continuousOn_moment β hβ μ _).mono hsub)))

end FRSB
