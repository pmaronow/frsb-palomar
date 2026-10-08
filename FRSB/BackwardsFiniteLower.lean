module

public import FRSB.BackwardsQNonnegative
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardClock (β t : ℝ) : ℝ := β ^ 2 * (1-t)

theorem backwardTime_clock (β : ℝ) (hβ : β ≠ 0) (t : ℝ) :
    backwardTime β (backwardClock β t) = t := by
  dsimp [backwardTime,backwardClock]
  field_simp
  ring

theorem backwardClock_cell_mem {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) {p : ℕ} {t : ℝ} (ht : t ∈ Icc (s.q p) (s.q (p+1))) :
    backwardClock β t ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p) := by
  dsimp [backwardClock,backwardCellStart,backwardCellEnd]
  constructor <;> nlinarith [sq_nonneg β,ht.1,ht.2]

theorem finiteScheme_backwardQ_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ backwardQ β (Paper.parisiSchemeMeasure s)
      (Paper.parisiCDF (Paper.parisiSchemeMeasure s) t) (t,x) := by
  by_cases ht1 : t = 1
  · subst t
    rw [Paper.parisiCDF_eq_one_of_one_le _ le_rfl,backwardQ_terminal β hβ _ x]
  obtain ⟨p,hp,hcell,hq⟩ := Paper.exists_parisiFinite_right_cell s
    (t := t) ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩
  rw [Paper.parisiCDF_scheme_cell s hp hcell]
  have he := finiteScheme_Q_nonneg_on_cells s β hβ hp (backwardClock_cell_mem s β ⟨hcell.1,hcell.2.le⟩) x
  simpa only [backwardTauQ,backwardTauD,backwardTime_clock β hβ,backwardQ,backwardC] using he

theorem finiteLaw_backwardQ_nonneg (μ : Paper.ParisiMeasure)
    (hμ : (μ : MeasureTheory.Measure Paper.Overlap).support.Finite)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ backwardQ β μ (Paper.parisiCDF μ t) (t,x) := by
  simpa only [parisiSchemeMeasure_finiteLawRSBScheme μ hμ] using
    finiteScheme_backwardQ_nonneg (finiteLawRSBScheme μ hμ) β hβ t x ht

end FRSB
