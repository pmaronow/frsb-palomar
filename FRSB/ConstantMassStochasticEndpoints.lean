module

public import FRSB.ConstantMassGaussianMoments
public import FRSB.StochasticCrops

@[expose] public section

/-! Literal closed-interval Cole--Hopf stochastic heat identity, realized
by genuinely adapted Brownian left sums on refining interior crops. Atoms
at either endpoint impose no temporal differentiability assumption. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000

theorem crop_observable_tendsto (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (β y m : ℝ) (l r : ℝ≥0) (hlr : l < r) (sample : BrownianSample) :
    Tendsto (fun n => Real.exp (m*f ((rightCellCrop l r n : ℝ),
      zeroDriftBrownian β (leftCellCrop l r n) y
        (rightCellCrop l r n-leftCellCrop l r n) sample))-
      Real.exp (m*f ((leftCellCrop l r n : ℝ),y))) atTop
      (𝓝 (Real.exp (m*f ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
        Real.exp (m*f ((l : ℝ),y)))) := by
  have hlt : (l : ℝ) < r := NNReal.coe_lt_coe.mpr hlr
  have hL : Tendsto (leftCellCrop l r) atTop (𝓝 l) := by
    simpa only [Real.toNNReal_coe] using tendsto_leftCellCrop l.coe_nonneg hlt
  have hR : Tendsto (rightCellCrop l r) atTop (𝓝 r) := by
    simpa only [Real.toNNReal_coe] using tendsto_rightCellCrop l.coe_nonneg hlt
  have hLc := NNReal.continuous_coe.tendsto l |>.comp hL
  have hRc := NNReal.continuous_coe.tendsto r |>.comp hR
  have hBL := (continuous_canonicalBrownian sample).tendsto l |>.comp hL
  have hBR := (continuous_canonicalBrownian sample).tendsto r |>.comp hR
  have hX : Tendsto (fun n => y+β*(canonicalBrownian (rightCellCrop l r n) sample-
      canonicalBrownian (leftCellCrop l r n) sample)) atTop
      (𝓝 (y+β*(canonicalBrownian r sample-canonicalBrownian l sample))) :=
    tendsto_const_nhds.add ((hBR.sub hBL).const_mul β)
  have hU := hf.tendsto ((r : ℝ),y+β*(canonicalBrownian r sample-canonicalBrownian l sample))
    |>.comp (hRc.prodMk_nhds hX)
  have hU0 := hf.tendsto ((l : ℝ),y) |>.comp (hLc.prodMk_nhds tendsto_const_nhds)
  have hh := ((Real.continuous_exp.tendsto _).comp (hU.const_mul m)).sub
    ((Real.continuous_exp.tendsto _).comp (hU0.const_mul m))
  have he (n : ℕ) : leftCellCrop l r n+(rightCellCrop l r n-leftCellCrop l r n)=
      rightCellCrop l r n := add_tsub_cancel_of_le (cellCrop_bounds l.coe_nonneg hlt n).2.1
  have he0 : l+(r-l)=r := add_tsub_cancel_of_le hlr.le
  simpa only [Function.comp_def,zeroDriftBrownian,canonicalDiracShiftMartingale,he,he0] using hh

theorem constantMassHeatStochasticLeftSums_closed (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (l r : ℝ≥0)
    (hl : a ≤ (l : ℝ)) (hlr : l < r) (hr : (r : ℝ) ≤ b) (y : ℝ) :
    ∃ mesh : ℕ → ℕ, (∀ n,n ≤ mesh n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (fun n => uniformAdaptedMartingaleLeftSumProcess
          (canonicalDiracShiftMartingale β (leftCellCrop l r n))
          (fun t sample => m*Real.exp (m*parisiPotential β μ
            ((leftCellCrop l r n : ℝ)+t,zeroDriftBrownian β (leftCellCrop l r n) y t sample))*
              parisiGradient β μ ((leftCellCrop l r n : ℝ)+t,
                zeroDriftBrownian β (leftCellCrop l r n) y t sample))
          (rightCellCrop l r n-leftCellCrop l r n) (mesh n+1)
          (rightCellCrop l r n-leftCellCrop l r n)) atTop
        (fun sample => Real.exp (m*parisiPotential β μ
          ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
            Real.exp (m*parisiPotential β μ ((l : ℝ),y))) := by
  let L := leftCellCrop l r
  let R := rightCellCrop l r
  let B := fun n sample => Real.exp (m*parisiPotential β μ
    ((R n : ℝ),zeroDriftBrownian β (L n) y (R n-L n) sample))-
      Real.exp (m*parisiPotential β μ ((L n : ℝ),y))
  have hlt : (l : ℝ) < r := NNReal.coe_lt_coe.mpr hlr
  have hcrop (n : ℕ) := cellCrop_bounds l.coe_nonneg hlt n
  have hL : Tendsto L atTop (𝓝 l) := by
    simpa only [Real.toNNReal_coe] using tendsto_leftCellCrop l.coe_nonneg hlt
  have hR : Tendsto R atTop (𝓝 r) := by
    simpa only [Real.toNNReal_coe] using tendsto_rightCellCrop l.coe_nonneg hlt
  have hB : TendstoInMeasure canonicalBrownianMeasure B atTop
      (fun sample => Real.exp (m*parisiPotential β μ
        ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
          Real.exp (m*parisiPotential β μ ((l : ℝ),y))) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      have hX := ((stronglyAdapted_zeroDriftBrownian β (L n) y) (R n-L n)).mono
        ((canonicalBrownianShiftFiltration (L n)).le (R n-L n))
      have hu : StronglyMeasurable (fun sample => parisiPotential β μ
          ((R n : ℝ),zeroDriftBrownian β (L n) y (R n-L n) sample)) :=
        (continuous_parisiPotential β μ).comp_stronglyMeasurable
          ((stronglyMeasurable_const (b := (R n : ℝ))).prodMk hX)
      exact ((Real.continuous_exp.comp_stronglyMeasurable (hu.const_mul m)).sub
        stronglyMeasurable_const).aestronglyMeasurable
    · exact .of_forall fun sample => crop_observable_tendsto
        (parisiPotential β μ) (continuous_parisiPotential β μ) β y m l r hlr sample
  have hA (n : ℕ) := constantMassHeatStochasticLeftSums β hβ μ ha hab hb hc (L n) (R n)
    (hl.trans_lt (hcrop n).1) (hcrop n).2.1 ((hcrop n).2.2.trans_le hr) y
  have hout := exists_diagonal_tendstoInMeasure hA hB
  exact hout

theorem memLp_two_constantMassHeat_difference (β : ℝ) (μ : ParisiMeasure) (m : ℝ)
    (l r : ℝ≥0) (hr : (r : ℝ) ≤ 1) (y : ℝ) :
    MemLp (fun sample => Real.exp (m*parisiPotential β μ
      ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
        Real.exp (m*parisiPotential β μ ((l : ℝ),y))) 2 canonicalBrownianMeasure :=
  (memLp_two_constantMassHeatObservable β μ r ⟨r.coe_nonneg,hr⟩ m l y (r-l)).sub (memLp_const _)

/-- The literal display-17 observable is an actual square-integrable,
mean-zero Brownian stochastic integral, with a constructed refining
adapted-sum realization and no supplied stochastic identity. -/
theorem constantMassHeat_stochastic_identity (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (l r : ℝ≥0)
    (hl : a ≤ (l : ℝ)) (hlr : l < r) (hr : (r : ℝ) ≤ b) (y : ℝ) :
    (∃ mesh : ℕ → ℕ, (∀ n,n ≤ mesh n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (fun n => uniformAdaptedMartingaleLeftSumProcess
          (canonicalDiracShiftMartingale β (leftCellCrop l r n))
          (fun t sample => m*Real.exp (m*parisiPotential β μ
            ((leftCellCrop l r n : ℝ)+t,zeroDriftBrownian β (leftCellCrop l r n) y t sample))*
              parisiGradient β μ ((leftCellCrop l r n : ℝ)+t,
                zeroDriftBrownian β (leftCellCrop l r n) y t sample))
          (rightCellCrop l r n-leftCellCrop l r n) (mesh n+1)
          (rightCellCrop l r n-leftCellCrop l r n)) atTop
        (fun sample => Real.exp (m*parisiPotential β μ
          ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
            Real.exp (m*parisiPotential β μ ((l : ℝ),y)))) ∧
    MemLp (fun sample => Real.exp (m*parisiPotential β μ
      ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
        Real.exp (m*parisiPotential β μ ((l : ℝ),y))) 2 canonicalBrownianMeasure ∧
    (∫ sample,Real.exp (m*parisiPotential β μ
      ((r : ℝ),zeroDriftBrownian β l y (r-l) sample))-
        Real.exp (m*parisiPotential β μ ((l : ℝ),y)) ∂canonicalBrownianMeasure)=0 :=
  ⟨constantMassHeatStochasticLeftSums_closed β hβ μ ha hab hb hc l r hl hlr hr y,
    memLp_two_constantMassHeat_difference β μ m l r (hr.trans hb) y,
    integral_constantMassHeat_difference_eq_zero β hβ μ ha hab hb hc l r
      ⟨hl,(NNReal.coe_lt_coe.mpr hlr).le.trans hr⟩ hlr.le hr y⟩

end FRSB
