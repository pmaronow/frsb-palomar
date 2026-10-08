module

public import FRSB.BackwardsInverseTime

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem hasDerivAt_constantCDF_backwardTauZ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ico a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardTauZ β μ (r, x))
      (backwardTauZt β μ m (τ, x)) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_backwardZJet
    (s := univ)
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 2 hτ x).hasDerivWithinAt
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 3 hτ x).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne')

theorem hasDerivAt_constantCDF_backwardTauP (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ico a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardTauP β μ m (r, x))
      (backwardTauPt β μ m (τ, x)) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_backwardWeightedQJet
    (s := univ) (a := m)
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 2 hτ x).hasDerivWithinAt
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 3 hτ x).hasDerivWithinAt
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 4 hτ x).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne')

theorem hasDerivAt_constantCDF_backwardTauR (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ico a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => backwardTauR β μ m (r, x))
      (backwardTauRt β μ m (τ, x)) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_backwardRJet
    (s := univ) (a := m)
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 2 hτ x).hasDerivWithinAt
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 3 hτ x).hasDerivWithinAt
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 4 hτ x).hasDerivWithinAt
    (hasDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 5 hτ x).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne')

/-- Lemma 3.3: the actual weighted Q equation on every actual constant-CDF interval. -/
theorem constantCDF_backward_weightedQ_equation (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ico a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => backwardTauP β μ m (r, x)) τ -
      deriv (deriv (fun y => backwardTauP β μ m (τ, y))) x / 2 -
      m * backwardTauD β μ 1 (τ, x) *
        deriv (fun y => backwardTauP β μ m (τ, y)) x =
      -2 * backwardTauQ β μ m (τ, x) *
        backwardTauP β μ m (τ, x) := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  rw [(hasDerivAt_constantCDF_backwardTauP β hβ μ ha hab hb hc hτ x).deriv,
    deriv_backwardTauP_spatial β hβ _ m τ hg,
    (hasDerivAt_backwardTauPx_spatial β hβ _ m τ x hg).deriv]
  dsimp [backwardTauPt, backwardTauPxx, backwardTauPx, backwardTauP, backwardTauQ]
  rw [backwardTauForcing_two, backwardTauForcing_three, backwardTauForcing_four]
  exact backward_weightedQ_evolution_jet _ _ _ _ _ _ _
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'

/-- Lemma 3.3: the actual CHx equation, including its nonnegative source. -/
theorem constantCDF_backward_weightedHx_equation (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ico a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => backwardTauR β μ m (r, x)) τ -
      deriv (deriv (fun y => backwardTauR β μ m (τ, y))) x / 2 -
      m * backwardTauD β μ 1 (τ, x) *
        deriv (fun y => backwardTauR β μ m (τ, y)) x =
      -5 * backwardTauQ β μ m (τ, x) *
        backwardTauR β μ m (τ, x) +
      6 * backwardTauD β μ 2 (τ, x) *
        backwardTauZ β μ (τ, x) *
        backwardTauQ β μ m (τ, x) ^ 2 := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  rw [(hasDerivAt_constantCDF_backwardTauR β hβ μ ha hab hb hc hτ x).deriv,
    deriv_backwardTauR_spatial β hβ _ m τ hg,
    (hasDerivAt_backwardTauRx_spatial β hβ _ m τ x hg).deriv]
  dsimp [backwardTauRt, backwardTauRxx, backwardTauRx, backwardTauR, backwardTauQ, backwardTauZ]
  rw [backwardTauForcing_two, backwardTauForcing_three, backwardTauForcing_four, backwardTauForcing_five]
  have hh := backward_weightedHx_evolution_jet m
    (backwardTauD β μ 1 (τ,x))
    (backwardTauD β μ 2 (τ,x))
    (backwardTauD β μ 3 (τ,x))
    (backwardTauD β μ 4 (τ,x))
    (backwardTauD β μ 5 (τ,x))
    (backwardTauD β μ 6 (τ,x))
    (backwardTauD β μ 7 (τ,x))
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'
  rw [← backwardRJet_eq_weightedHx _ _ _ _ _
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'] at hh
  exact hh

theorem constantCDF_backward_z_equation (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ico a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ) :
    deriv (fun r => backwardTauZ β μ (r, x)) τ -
      deriv (deriv (fun y => backwardTauZ β μ (τ, y))) x / 2 -
      m * backwardTauD β μ 1 (τ, x) *
        deriv (fun y => backwardTauZ β μ (τ, y)) x =
      -2 * backwardTauQ β μ m (τ, x) *
        backwardTauZ β μ (τ, x) := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  have ht := backwardTime_mem β hβ τ hg
  have he : deriv (fun y => backwardTauZ β μ (τ,y)) =
      fun y => backwardZx β μ (backwardTime β τ,y) :=
    funext fun y => (hasDerivAt_backwardZ β hβ _ _ y ht).deriv
  rw [(hasDerivAt_constantCDF_backwardTauZ β hβ μ ha hab hb hc hτ x).deriv, he,
    (hasDerivAt_backwardZx β hβ _ _ x ht).deriv]
  dsimp [backwardTauZt, backwardTauQ, backwardTauZ, backwardZx, backwardZxx]
  rw [backwardTauForcing_two, backwardTauForcing_three]
  exact backward_z_evolution_jet _ _ _ _ _ _ (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'


end FRSB
