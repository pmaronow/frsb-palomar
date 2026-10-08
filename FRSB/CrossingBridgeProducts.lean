module

public import FRSB.CrossingBridgeIntegrability
public import FRSB.BackwardsSmooth

@[expose] public section

/-! All products used in the crossing covariances are genuinely integrable.
The only unbounded observable is K, controlled by a quadratic spatial tail. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB
set_option maxHeartbeats 1000000

def bridgeCrossingKBound (β s : ℝ) : ℝ :=
  2 * ((β ^ 2 * s)⁻¹ ^ 2 + 9) + (β ^ 2 * s)⁻¹ +
    |negativeLogDerivativeConstant (forwardBridgeRelativeConstant β 2) 2| + 2

theorem norm_bridgeCrossingK_quadratic (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖bridgeCrossingK β μ s hs x‖ ≤ bridgeCrossingKBound β s * (1 + |x| ^ 2) := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  let a := (β ^ 2 * s)⁻¹
  let c := a + |negativeLogDerivativeConstant (forwardBridgeRelativeConstant β 2) 2|
  have ha : 0 ≤ a := inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le
  have hc : 0 ≤ c := add_nonneg ha (abs_nonneg _)
  have hN : ‖bridgeCrossingN β μ s hs x‖ ≤ a * |x| + 3 := by
    simpa only [a,div_eq_mul_inv,mul_comm] using norm_bridgeCrossingN_linear β hβ μ s hs x
  have hN2 : ‖bridgeCrossingN β μ s hs x‖ ^ 2 ≤ (a * |x| + 3) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hN 2
  have hV : ‖bridgeCrossingVxx β μ s hs x‖ ≤ c := by
    unfold bridgeCrossingVxx
    apply (norm_add_le _ _).trans
    rw [Real.norm_of_nonneg ha]
    dsimp only [c]
    gcongr
    exact (forwardBridgeCorrection_uniform_derivative_bound β μ s hs 2
      (by norm_num) x).trans (le_abs_self _)
  have hz : ‖backwardZ β μ (s,x)‖ ^ 2 ≤ 1 := by
    apply pow_le_one₀ (norm_nonneg _)
    simpa only [Real.norm_eq_abs] using backwardZ_abs_le_one_crossing β hβ μ s x ht
  have hmC : ‖parisiCDF μ s * backwardC β μ (s,x)‖ ≤ 1 := by
    rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ s),
      Real.norm_of_nonneg (backwardC_pos β hβ μ s x ht).le]
    exact (mul_le_mul (parisiCDF_le_one μ s) (backwardC_le_one β hβ μ s x ht)
      (backwardC_pos β hβ μ s x ht).le zero_le_one).trans_eq (mul_one _)
  have hnorm : ‖bridgeCrossingK β μ s hs x‖ ≤
      ‖bridgeCrossingN β μ s hs x‖ ^ 2 + c + 2 := by
    unfold bridgeCrossingK crossingK
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    apply (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans
    rw [norm_pow,norm_pow]
    linarith
  have hsq : (a * |x| + 3) ^ 2 ≤ 2 * a ^ 2 * |x| ^ 2 + 18 := by
    nlinarith [sq_nonneg (a*|x|-3)]
  apply hnorm.trans
  have he : bridgeCrossingKBound β s = 2 * (a ^ 2 + 9) + c + 2 := by
    dsimp only [bridgeCrossingKBound,a,c]
    ring
  rw [he]
  nlinarith [mul_nonneg hc (sq_nonneg |x|),sq_nonneg a,sq_nonneg |x|]

theorem integrable_bridgeCrossingK (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (bridgeCrossingK β μ s hs)
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  apply integrable_bridgeCrossingWeightLaw_of_polynomial_growth β hβ μ s hs _
    (continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_bridgeCrossingK β hβ μ s hs x).continuousAt))
    2 (bridgeCrossingKBound β s)
  · have ha := inv_nonneg.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le
    unfold bridgeCrossingKBound
    positivity
  · exact fun x _ => norm_bridgeCrossingK_quadratic β hβ μ s hs x

theorem integrable_bridgeCrossingH (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => backwardH β μ (parisiCDF μ s) (s,x))
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) := by
  let := bridgeCrossingWeightLaw_isProbability β hβ μ s hs
  apply (integrable_const (4 : ℝ)).mono'
    ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_backwardH β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩).continuousAt).aestronglyMeasurable)
  exact .of_forall fun x => norm_backwardH_le_four_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩

theorem integrable_bridgeCrossingPhi_mul_K (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x) * bridgeCrossingK β μ s hs x)
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) :=
  (integrable_bridgeCrossingK β hβ μ s hs).bdd_mul
    ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_actualCrossingPhi β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩).continuousAt).aestronglyMeasurable)
    (.of_forall fun x => norm_actualCrossingPhi_le_three β hβ μ s x ⟨hs.1.le,hs.2⟩)

theorem integrable_bridgeCrossingH_mul_Psi (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun x => backwardH β μ (parisiCDF μ s) (s,x) * bridgeCrossingPsi β μ s hs x)
      (crossingWeightLaw (bridgeCrossingWeight β μ s hs)) :=
  (integrable_bridgeCrossingPsi β hβ μ s hs).bdd_mul
    ((continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_backwardH β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩).continuousAt).aestronglyMeasurable)
    (.of_forall fun x => norm_backwardH_le_four_crossing β hβ μ s x ⟨hs.1.le,hs.2⟩)

end FRSB
