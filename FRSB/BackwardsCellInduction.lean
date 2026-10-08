module

public import FRSB.BackwardsEquations
public import FRSB.MeasureCellInduction

@[expose] public section

open Set
namespace FRSB

/-- Backward closed-cell induction retaining the actual mass on each cell.
The jump input is separated from the continuous evolution input. -/
theorem backward_scheme_coefficient_induction {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (P : ℝ → ℝ → Prop) (hbase : P 1 0)
    (hstep : ∀ p ≤ k+1, P (s.m p) (backwardCellStart s β p) →
      ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), P (s.m p) τ)
    (hjump : ∀ p ≤ k, P (s.m (p+1)) (backwardCellStart s β p) →
      P (s.m p) (backwardCellStart s β p)) :
    ∀ p ≤ k+1, ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), P (s.m p) τ := by
  intro p hp
  apply Nat.decreasingInduction (n := k+1)
    (motive := fun p _ => ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), P (s.m p) τ)
    ?_ ?_ hp
  · intro p hptop hnext
    apply hstep p hptop.le
    apply hjump p (by omega)
    apply hnext (backwardCellStart s β p)
    constructor
    · have hq := s.q_mono (p+1) (by omega)
      dsimp [backwardCellStart]
      nlinarith [sq_nonneg β]
    · rfl
  · apply hstep (k+1) le_rfl
    simpa [s.m_top,backwardCellStart,s.q_top] using hbase

end FRSB
