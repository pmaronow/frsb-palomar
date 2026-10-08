module

public import FRSB.BackwardsMagnetization
public import FRSB.BackwardsConstantTime

@[expose] public section

/-! Genuine implicit time differentiation of the global inverse
magnetization coordinate on every actual constant-CDF interval. -/
noncomputable section
open Set Filter Paper
open scoped Topology
namespace FRSB

theorem backwardTime_mem_converse (β : ℝ) (hβ : β ≠ 0) (τ : ℝ)
    (ht : backwardTime β τ ∈ Icc (0 : ℝ) 1) : τ ∈ Icc (0 : ℝ) (β^2) := by
  have he : β^2 * backwardTime β τ = β^2 - τ := by
    dsimp [backwardTime]
    field_simp
  have hp := sq_pos_of_ne_zero hβ
  constructor <;> nlinarith [mul_nonneg hp.le ht.1,mul_le_mul_of_nonneg_left ht.2 hp.le]

theorem continuous_backwardTauForcing (β : ℝ) (μ : ParisiMeasure) (m : ℝ) (j : ℕ) :
    Continuous (backwardTauForcing β μ m j) := by
  unfold backwardTauForcing
  apply Continuous.div_const
  apply Continuous.add (continuous_backwardTauD β μ (j+2))
  apply Continuous.const_mul
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_backwardTauD β μ (i+1)).const_mul _).mul
      (continuous_backwardTauD β μ (j-i+1))

theorem hasStrictFDerivAt_constantCDF_backwardTauD (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (j : ℕ)
    {τ x : ℝ} (hτ : backwardTime β τ ∈ Ioo a b) :
    HasStrictFDerivAt (backwardTauD β μ j)
      ((ContinuousLinearMap.toSpanSingleton ℝ (backwardTauForcing β μ m j (τ,x))).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (backwardTauD β μ (j+1) (τ,x)))) (τ,x) := by
  have hmap : Continuous (fun p : ℝ×ℝ => backwardTime β p.1) := by
    dsimp [backwardTime]
    fun_prop
  have hnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (τ,x), backwardTime β p.1 ∈ Ioo a b :=
    hmap.continuousAt.eventually (isOpen_Ioo.mem_nhds hτ)
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun r y => backwardTauD β μ j (r,y)) (u := (τ,x))
    (f₁ := fun r y => ContinuousLinearMap.toSpanSingleton ℝ (backwardTauForcing β μ m j (r,y)))
    (f₂ := fun r y => ContinuousLinearMap.toSpanSingleton ℝ (backwardTauD β μ (j+1) (r,y)))
  · filter_upwards [hnear] with p hp
    exact (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc j hp p.2).hasFDerivAt
  · filter_upwards [hnear] with p hp
    have hg := backwardTime_mem_converse β hβ p.1 ⟨ha.trans hp.1.le,hp.2.le.trans hb⟩
    exact (hasDerivAt_backwardTauD_spatial β hβ μ j p.1 p.2 hg).hasFDerivAt
  · exact ((ContinuousLinearMap.toSpanSingletonCLE :
      ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp (continuous_backwardTauForcing β μ m j)).continuousAt
  · exact ((ContinuousLinearMap.toSpanSingletonCLE :
      ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.comp (continuous_backwardTauD β μ (j+1))).continuousAt

theorem differentiableAt_backwardMagnetizationInverse_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ (fun r => backwardMagnetizationInverse β μ r v) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  let x := backwardMagnetizationInverse β μ τ v
  have hstrict := hasStrictFDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 1 (x := x) hτ
  have hinv : (((ContinuousLinearMap.toSpanSingleton ℝ (backwardTauForcing β μ m 1 (τ,x))).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ (backwardTauD β μ 2 (τ,x)))) ∘L
        ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    simpa using scalarCLM_isInvertible (backwardTauD β μ 2 (τ,x))
      (backwardTauC_pos_le_one β hβ μ τ x hg).1.ne'
  let ψ := hstrict.implicitFunctionOfProdDomain hinv
  have happ := hstrict.eventually_apply_implicitFunctionOfProdDomain hinv
  have hmap : Continuous (backwardTime β) := continuous_const.sub (continuous_id.div_const (β^2))
  have hnear := hmap.continuousAt.eventually (isOpen_Ioo.mem_nhds hτ)
  have he : (fun r => backwardMagnetizationInverse β μ r v) =ᶠ[𝓝 τ] ψ := by
    filter_upwards [happ,hnear] with r hr hp
    have hrg := backwardTime_mem_converse β hβ r ⟨ha.trans hp.1.le,hp.2.le.trans hb⟩
    have heB : backwardTauD β μ 1 (r,ψ r) = v := by
      exact hr.trans (backwardMagnetizationInverse_eq β hβ μ τ v hg hv)
    apply (parisiGradient_strictMono β hβ μ (backwardTime β r)
      ⟨ha.trans hp.1.le,hp.2.le.trans hb⟩).injective
    have hi := backwardMagnetizationInverse_eq β hβ μ r v hrg hv
    simpa only [backwardTauD,show backwardD β μ 1 = backwardB β μ from rfl,
      backwardB_eq_gradient β μ (backwardTime β r) _ ⟨ha.trans hp.1.le,hp.2.le.trans hb⟩] using hi.trans heB.symm
  exact (hstrict.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt
    |>.congr_of_eventuallyEq he

theorem hasDerivAt_backwardMagnetizationInverse_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => backwardMagnetizationInverse β μ r v)
      (backwardTauZ β μ (τ,backwardMagnetizationInverse β μ τ v) - m*v) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  let x := backwardMagnetizationInverse β μ τ v
  have hroot := (differentiableAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc hτ hv).hasDerivAt
  have htotal := (hasStrictFDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 1 (x := x) hτ).hasFDerivAt
    |>.comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk hroot)
  have hmap : Continuous (backwardTime β) := continuous_const.sub (continuous_id.div_const (β^2))
  have he : (fun r => backwardTauD β μ 1 (r,backwardMagnetizationInverse β μ r v)) =ᶠ[𝓝 τ]
      (fun _ => v) := by
    filter_upwards [hmap.continuousAt.eventually (isOpen_Ioo.mem_nhds hτ)] with r hr
    exact backwardMagnetizationInverse_eq β hβ μ r v
      (backwardTime_mem_converse β hβ r ⟨ha.trans hr.1.le,hr.2.le.trans hb⟩) hv
  have hz := (hasDerivAt_const τ v).congr_of_eventuallyEq he
  have hid := htotal.unique hz
  simp only [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul] at hid
  rw [backwardTauForcing_one,backwardMagnetizationInverse_eq β hβ μ τ v hg hv] at hid
  have hp := (backwardTauC_pos_le_one β hβ μ τ x hg).1
  have hd : deriv (fun r => backwardMagnetizationInverse β μ r v) τ =
      backwardTauZ β μ (τ,x)-m*v := by
    dsimp [backwardTauZ,backwardZ,backwardZJet,backwardTauD,backwardC] at *
    apply (eq_sub_iff_add_eq).mpr
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hp.ne')).mpr
    nlinarith
  rwa [hd] at hroot

end FRSB
