module

public import FRSB.BackwardsRelativeFinite

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardNormalizedFields (p : (ℝ × ℝ) × (ℝ × ℝ × ℝ)) : ℝ × ℝ × ℝ :=
  (-p.2.1 / 2, -p.2.2.1 / 2 + p.2.1 ^ 2 / 2 - p.1.1 * p.1.2,
    p.2.2.2 - 5 * p.2.1 * p.2.2.1 / 2 + 3 * p.2.1 ^ 3 / 2 + 3 * p.1.1 * p.1.2 * p.2.1)

theorem exists_backwardJet_bound (K3 K4 K5 : ℝ) :
    ∃ M > 0, ∀ a C D E F : ℝ, a ∈ Icc (0 : ℝ) 1 → 0 < C → C ≤ 1 →
      |D| ≤ K3 * C → |E| ≤ K4 * C → |F| ≤ K5 * C →
      |backwardZJet C D| ≤ M ∧ |backwardQJet a C D E| ≤ M ∧ |backwardHxJet a C D E F| ≤ M := by
  let box := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ
    (Icc (-K3) K3 ×ˢ (Icc (-K4) K4 ×ˢ Icc (-K5) K5))
  have hc : IsCompact box := isCompact_Icc.prod isCompact_Icc |>.prod
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hf : Continuous backwardNormalizedFields := by
    unfold backwardNormalizedFields
    fun_prop
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨|M|+1,by positivity,?_⟩
  intro a C D E F ha hC hC1 hD hE hF
  have hd : |D/C| ≤ K3 := by
    rw [abs_div,abs_of_pos hC]
    exact (div_le_iff₀ hC).mpr hD
  have he : |E/C| ≤ K4 := by
    rw [abs_div,abs_of_pos hC]
    exact (div_le_iff₀ hC).mpr hE
  have hf0 : |F/C| ≤ K5 := by
    rw [abs_div,abs_of_pos hC]
    exact (div_le_iff₀ hC).mpr hF
  let p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) := ((a,C),(D/C,E/C,F/C))
  have hp : p ∈ box := ⟨⟨ha,⟨hC.le,hC1⟩⟩,abs_le.mp hd,abs_le.mp he,abs_le.mp hf0⟩
  have hh : ‖backwardNormalizedFields p‖ ≤ |M|+1 :=
    (hM p hp).trans (by linarith [le_abs_self M])
  have h1 : |(backwardNormalizedFields p).1| ≤ |M|+1 := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le (backwardNormalizedFields p)).trans hh
  have h2 : |(backwardNormalizedFields p).2.1| ≤ |M|+1 := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le (backwardNormalizedFields p).2).trans
      ((norm_snd_le (backwardNormalizedFields p)).trans hh)
  have h3 : |(backwardNormalizedFields p).2.2| ≤ |M|+1 := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le (backwardNormalizedFields p).2).trans
      ((norm_snd_le (backwardNormalizedFields p)).trans hh)
  have hz : backwardZJet C D = (backwardNormalizedFields p).1 := by
    dsimp [backwardZJet,backwardNormalizedFields,p]
    ring
  have hq : backwardQJet a C D E = (backwardNormalizedFields p).2.1 := by
    dsimp [backwardQJet,backwardZxJet,backwardNormalizedFields,p]
    field_simp
  have hhx : backwardHxJet a C D E F = (backwardNormalizedFields p).2.2 := by
    dsimp [backwardHxJet,backwardQxJet,backwardZxxJet,backwardZJet,backwardZxJet,
      backwardNormalizedFields,p]
    field_simp
    ring
  simpa only [hz,hq,hhx] using And.intro h1 (And.intro h2 h3)

def backwardRationalBound (β : ℝ) : ℝ :=
  (exists_backwardJet_bound (backwardRelativeK3 β) (backwardRelativeK4 β) (backwardRelativeK5 β)).choose

theorem backwardRationalBound_pos (β : ℝ) : 0 < backwardRationalBound β :=
  (exists_backwardJet_bound (backwardRelativeK3 β) (backwardRelativeK4 β) (backwardRelativeK5 β)).choose_spec.1

theorem finiteScheme_backward_fields_bounded {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) (x : ℝ) :
    |backwardTauZ β (Paper.parisiSchemeMeasure s) (τ,x)| ≤ backwardRationalBound β ∧
    |backwardTauQ β (Paper.parisiSchemeMeasure s) a (τ,x)| ≤ backwardRationalBound β ∧
    |backwardHx β (Paper.parisiSchemeMeasure s) a (backwardTime β τ,x)| ≤ backwardRationalBound β :=
  (exists_backwardJet_bound (backwardRelativeK3 β) (backwardRelativeK4 β) (backwardRelativeK5 β)).choose_spec.2
    a _ _ _ _ ha (backwardTauC_pos_le_one β hβ _ τ x hτ).1
    (backwardTauC_pos_le_one β hβ _ τ x hτ).2
    (finiteScheme_D3_relative s β hβ hτ x) (finiteScheme_D4_relative s β hβ hτ x)
    (finiteScheme_D5_relative s β hβ hτ x)

theorem finiteScheme_backward_weighted_fields_bounded {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) (x : ℝ) :
    |backwardTauP β (Paper.parisiSchemeMeasure s) a (τ,x)| ≤ backwardRationalBound β ∧
    |backwardTauR β (Paper.parisiSchemeMeasure s) a (τ,x)| ≤ backwardRationalBound β := by
  have hc := backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) τ x hτ
  have hb := finiteScheme_backward_fields_bounded s β hβ a ha hτ x
  constructor
  · dsimp [backwardTauP]
    rw [abs_mul,abs_of_pos hc.1]
    exact (mul_le_mul_of_nonneg_right hc.2 (abs_nonneg _)).trans (by simpa using hb.2.1)
  · rw [backwardTauR_eq_weightedHx β hβ _ a τ x hτ,abs_mul,abs_of_pos hc.1]
    exact (mul_le_mul_of_nonneg_right hc.2 (abs_nonneg _)).trans (by simpa using hb.2.2)

end FRSB
