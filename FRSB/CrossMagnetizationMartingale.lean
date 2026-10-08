module

public import FRSB.CrossMagnetizationRemark

@[expose] public section

/-! The drift-free magnetization density satisfies its actual diffusion
PDE. Its spatial diffusion coefficient is the genuine susceptibility. -/
noncomputable section
open Set Paper
namespace FRSB

 def magnetizationEta (β : ℝ) (μ : ParisiMeasure) (s v : ℝ) : ℝ :=
  magnetizationR β μ s v / backwardC β μ (s,magnetizationInverse β μ s v)^2

 theorem magnetizationEta_eq_density (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (v : ℝ) :
    magnetizationEta β μ s v = magnetizationDensity β μ s hs v := by
  rw [magnetizationEta,magnetizationR_eq_weightedDensity β μ s hs]
  have hC := (backwardC_pos β hβ μ s (magnetizationInverse β μ s v) ⟨hs.1.le,hs.2⟩).ne'
  unfold magnetizationWeightedDensity magnetizationDensity
  field_simp

 theorem hasDerivAt_magnetizationEta_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {s v : ℝ}
    (hs : s ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => magnetizationEta β μ r v)
      ((β^2/2)*deriv (deriv (magnetizationR β μ s)) v) s := by
  have hC := (backwardC_pos β hβ μ s (magnetizationInverse β μ s v)
    ⟨ha.trans hs.1.le,hs.2.le.trans hb⟩).ne'
  have hR := hasDerivAt_magnetizationR_time β hβ μ ha hab hb hc hs hv
  have hχ := hasDerivAt_magnetizationCurvature_time β hβ μ ha hab hb hc hs hv
  have hd := hR.div (hχ.pow 2) (pow_ne_zero 2 hC)
  have he := magnetizationR_weighted_law β hβ μ ha hab hb hc hs hv
  rw [hR.deriv] at he
  convert hd using 1
  · rfl
  · rw [he]
    norm_num only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one]
    field_simp
    ring

 def forwardMagnetizationEta (β : ℝ) (μ : ParisiMeasure) (t v : ℝ) : ℝ :=
  magnetizationEta β μ (t/β^2) v

 theorem forwardMagnetizationEta_diffusion_equation (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun r => forwardMagnetizationEta β μ r v) t =
      (1/2:ℝ)*deriv (deriv (forwardMagnetizationR β μ t)) v := by
  have hd := (hasDerivAt_magnetizationEta_time β hβ μ ha hab hb hc ht hv).comp t
    ((hasDerivAt_id t).div_const (β^2))
  have hfn : (fun r => forwardMagnetizationEta β μ r v) =
      (fun s => magnetizationEta β μ s v) ∘ (fun r => r/β^2) := rfl
  simp only [id_eq] at hd
  rw [hfn,hd.deriv]
  have hsp : forwardMagnetizationR β μ t = magnetizationR β μ (t/β^2) := rfl
  rw [hsp]
  field_simp

end FRSB
