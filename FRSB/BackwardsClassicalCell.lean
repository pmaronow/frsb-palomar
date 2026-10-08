module

public import FRSB.ComparisonInterior

@[expose] public section

noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

structure IsBoundedClassicalCell (a c : ℝ) (v : ℝ × ℝ → ℝ) : Prop where
  continuous : ContinuousOn v (Icc a c ×ˢ univ)
  bounded : ∃ M ≥ 0, ∀ t ∈ Icc a c, ∀ x, |v (t,x)| ≤ M
  time : ∀ t ∈ Ioo a c, ∀ x, DifferentiableAt ℝ (fun r => v (r,x)) t
  space : ∀ t ∈ Icc a c, ∀ x, DifferentiableAt ℝ (fun y => v (t,y)) x
  space2 : ∀ t ∈ Icc a c, ∀ x, DifferentiableAt ℝ (deriv (fun y => v (t,y))) x

theorem IsBoundedClassicalCell.sub {a c : ℝ} {v w : ℝ × ℝ → ℝ}
    (hv : IsBoundedClassicalCell a c v) (hw : IsBoundedClassicalCell a c w) :
    IsBoundedClassicalCell a c (fun p => v p - w p) := by
  refine ⟨hv.continuous.sub hw.continuous,?_,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hv.bounded
    obtain ⟨N,hN,hb'⟩ := hw.bounded
    refine ⟨M+N,add_nonneg hM hN,fun t ht x => ?_⟩
    have htri : |v (t,x)-w (t,x)| ≤ |v (t,x)|+|w (t,x)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (v (t,x)) (w (t,x))
    exact htri.trans (add_le_add (hb t ht x) (hb' t ht x))
  · exact fun t ht x => (hv.time t ht x).sub (hw.time t ht x)
  · exact fun t ht x => (hv.space t ht x).sub (hw.space t ht x)
  · intro t ht x
    have he : deriv (fun y => v (t,y)-w (t,y)) =
        fun y => deriv (fun z => v (t,z)) y - deriv (fun z => w (t,z)) y :=
      funext fun y => deriv_sub (hv.space t ht y) (hw.space t ht y)
    rw [he]
    exact (hv.space2 t ht x).sub (hw.space2 t ht x)

theorem IsBoundedClassicalCell.const_mul {a c d : ℝ} {v : ℝ × ℝ → ℝ}
    (hv : IsBoundedClassicalCell a c v) : IsBoundedClassicalCell a c (fun p => d*v p) := by
  refine ⟨hv.continuous.const_mul d,?_,?_,?_,?_⟩
  · obtain ⟨M,hM,hb⟩ := hv.bounded
    refine ⟨|d| * M,mul_nonneg (abs_nonneg _) hM,fun t ht x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb t ht x) (abs_nonneg _)
  · exact fun t ht x => (hv.time t ht x).const_mul d
  · exact fun t ht x => (hv.space t ht x).const_mul d
  · intro t ht x
    have he : deriv (fun y => d*v (t,y)) = fun y => d*deriv (fun z => v (t,z)) y :=
      funext fun y => deriv_const_mul d (hv.space t ht y)
    rw [he]
    exact (hv.space2 t ht x).const_mul d

theorem IsBoundedClassicalCell.const (a c d : ℝ) :
    IsBoundedClassicalCell a c (fun _ => d) := by
  refine ⟨continuous_const.continuousOn,⟨|d|,abs_nonneg _,fun _ _ _ => le_rfl⟩,
    fun _ _ _ => differentiableAt_const _,fun _ _ _ => differentiableAt_const _,?_⟩
  intro t ht x
  have he : deriv (fun _ : ℝ => d) = fun _ : ℝ => (0 : ℝ) := funext fun y => deriv_const y d
  rw [he]
  exact differentiableAt_const _

def backwardGenerator (b v : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun r => v (r,p.2)) p.1 - deriv (deriv (fun y => v (p.1,y))) p.2 / 2 -
    b p * deriv (fun y => v (p.1,y)) p.2

theorem backwardGenerator_sub {a c : ℝ} {v w : ℝ × ℝ → ℝ}
    (hv : IsBoundedClassicalCell a c v) (hw : IsBoundedClassicalCell a c w)
    (b : ℝ × ℝ → ℝ) {t : ℝ} (ht : t ∈ Ioo a c) (x : ℝ) :
    backwardGenerator b (fun p => v p-w p) (t,x) =
      backwardGenerator b v (t,x)-backwardGenerator b w (t,x) := by
  have he : deriv (fun y => v (t,y)-w (t,y)) =
      fun y => deriv (fun z => v (t,z)) y - deriv (fun z => w (t,z)) y :=
    funext fun y => deriv_sub (hv.space t ⟨ht.1.le,ht.2.le⟩ y) (hw.space t ⟨ht.1.le,ht.2.le⟩ y)
  dsimp [backwardGenerator]
  have ht0 : HasDerivAt (fun r => v (r,x)-w (r,x))
      (deriv (fun r => v (r,x)) t - deriv (fun r => w (r,x)) t) t :=
    (hv.time t ht x).hasDerivAt.sub (hw.time t ht x).hasDerivAt
  have hx0 : HasDerivAt (fun y => deriv (fun z => v (t,z)) y - deriv (fun z => w (t,z)) y)
      (deriv (deriv (fun z => v (t,z))) x - deriv (deriv (fun z => w (t,z))) x) x :=
    (hv.space2 t ⟨ht.1.le,ht.2.le⟩ x).hasDerivAt.sub (hw.space2 t ⟨ht.1.le,ht.2.le⟩ x).hasDerivAt
  rw [ht0.deriv,he,hx0.deriv]
  ring

theorem backwardGenerator_const_mul {a c d : ℝ} {v : ℝ × ℝ → ℝ}
    (hv : IsBoundedClassicalCell a c v) (b : ℝ × ℝ → ℝ) {t : ℝ} (ht : t ∈ Ioo a c) (x : ℝ) :
    backwardGenerator b (fun p => d*v p) (t,x) = d*backwardGenerator b v (t,x) := by
  have he : deriv (fun y => d*v (t,y)) = fun y => d*deriv (fun z => v (t,z)) y :=
    funext fun y => deriv_const_mul d (hv.space t ⟨ht.1.le,ht.2.le⟩ y)
  dsimp [backwardGenerator]
  rw [deriv_const_mul d (hv.time t ht x),he,
    deriv_const_mul d (hv.space2 t ⟨ht.1.le,ht.2.le⟩ x)]
  ring

theorem backwardGenerator_const (b : ℝ × ℝ → ℝ) (d : ℝ) (p : ℝ × ℝ) :
    backwardGenerator b (fun _ => d) p = 0 := by simp [backwardGenerator]

theorem IsBoundedClassicalCell.supersolution_nonneg {a c : ℝ} {v : ℝ × ℝ → ℝ}
    (hv : IsBoundedClassicalCell a c v) (hac : a ≤ c) (halfLine : Bool) (b κ : ℝ × ℝ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine, b (t,x)*sign x ≤ K)
    (hκ : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine, κ (t,x) ≤ K)
    (hsource : ∀ t ∈ Ioo a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      0 ≤ backwardGenerator b v (t,x)-κ (t,x)*v (t,x))
    (hinitial : ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (a,x))
    (hboundary : halfLine = true → ∀ t ∈ Icc a c, 0 ≤ v (t,0)) :
    ∀ t ∈ Icc a c, ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (t,x) := by
  obtain ⟨M,hM,hMv⟩ := hv.bounded
  have he := interval_supersolution_nonneg_interior halfLine a c K M hac hK hM v
    (fun p => deriv (fun r => v (r,p.2)) p.1) b κ
    (hv.continuous.mono (prod_mono (Subset.refl _) (subset_univ _)))
    (fun t ht x _ => (hv.time t ht x).hasDerivAt)
    (fun t ht x _ => hv.space t ⟨ht.1.le,ht.2.le⟩ x)
    (fun t ht x _ => hv.space2 t ⟨ht.1.le,ht.2.le⟩ x)
    (fun t ht x _ => hMv t ht x) hb hκ
    (fun t ht x hx => by
      have hh := hsource t ht x hx
      dsimp [backwardGenerator] at hh
      nlinarith)
    hinitial hboundary
  exact fun t ht x hx => he (t,x) ⟨ht,hx⟩

end FRSB
