module

public import FRSB.ForwardSchemeHistory
public import FRSB.BrownianMarkov

@[expose] public section

/-! Exact finite-scheme optimal-state joint laws as a density relative to the
actual scaled canonical Brownian joint law. The density retains all overlap
nodes, including repeated endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper SpinGlass.Targets
open scoped NNReal ENNReal Topology
namespace FRSB

def forwardGaussianKernel {k : ℕ} (s : RSBScheme k) (β : ℝ) (t : ℝ≥0)
    (j : ℕ) : Kernel ℝ ℝ := gaussianStateKernel
      (β^2*((forwardSchemeTime s t (j+1):ℝ)-forwardSchemeTime s t j)).toNNReal

instance {k : ℕ} (s : RSBScheme k) (β : ℝ) (t : ℝ≥0) (j : ℕ) :
    IsMarkovKernel (forwardGaussianKernel s β t j) :=
  inferInstanceAs (IsMarkovKernel (gaussianStateKernel _))

def forwardSchemeWeight {k : ℕ} (s : RSBScheme k) (β : ℝ) (t : ℝ≥0)
    (j : ℕ) (x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (forwardSchemeMass s j *
    (parisiPotential β (parisiSchemeMeasure s) (forwardSchemeTime s t (j+1),y) -
     parisiPotential β (parisiSchemeMeasure s) (forwardSchemeTime s t j,x))))

theorem measurable_forwardSchemeWeight {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (t : ℝ≥0) (j : ℕ) : Measurable (Function.uncurry (forwardSchemeWeight s β t j)) := by
  apply Measurable.ennreal_ofReal
  apply Continuous.measurable
  have hdiff : Continuous (fun p : ℝ × ℝ =>
      parisiPotential β (parisiSchemeMeasure s) (forwardSchemeTime s t (j+1),p.2) -
      parisiPotential β (parisiSchemeMeasure s) (forwardSchemeTime s t j,p.1)) :=
    ((continuous_parisiPotential β _).comp (continuous_const.prodMk continuous_snd)).sub
      ((continuous_parisiPotential β _).comp (continuous_const.prodMk continuous_fst))
  exact Real.continuous_exp.comp (hdiff.const_mul _)

theorem forwardSchemeKernel_eq_withDensity {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (hβ : β ≠ 0) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (j : ℕ) :
    forwardSchemeKernel s β t j = (forwardGaussianKernel s β t j).withDensity
      (forwardSchemeWeight s β t j) := by
  let a := forwardSchemeTime s t j
  let b := forwardSchemeTime s t (j+1)
  have hab : a ≤ b := forwardSchemeTime_monotone s t (Nat.le_succ j)
  have hab1 : (a:ℝ)+(b-a:ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_add, add_tsub_cancel_of_le hab]
    exact (show (b:ℝ) ≤ t from forwardSchemeTime_le s t (j+1)).trans ht
  have hvar : β^2*(b-a:ℝ≥0) = β^2*((b:ℝ)-a) := by
    rw [NNReal.coe_sub hab]
  ext x : 1
  rw [Kernel.withDensity_apply _ (measurable_forwardSchemeWeight s β t j)]
  by_cases he : a = b
  · change parisiConstantMassKernel β (parisiSchemeMeasure s) a (b-a) _ x =
      (gaussianReal x (β^2*((b:ℝ)-a)).toNNReal).withDensity _
    rw [← he, tsub_self]
    simp only [parisiConstantMassKernel, NNReal.coe_zero, mul_zero, Real.toNNReal_zero,add_zero]
    have hAc : Continuous (fun y : ℝ => parisiPotential β (parisiSchemeMeasure s) (a,y)) :=
      (continuous_parisiPotential β _).comp (continuous_const.prodMk continuous_id)
    have hAg := parisiPotential_hasLinearGrowth β (parisiSchemeMeasure s) a
      ⟨a.coe_nonneg, (show (a:ℝ) ≤ t from forwardSchemeTime_le s t j).trans ht⟩
    rw [constantMassKernel_zero_variance _ _ hAc hAg]
    change Measure.dirac x = (gaussianReal x (β^2*((a:ℝ)-a)).toNNReal).withDensity
      (forwardSchemeWeight s β t j x)
    simp only [sub_self,mul_zero,Real.toNNReal_zero,gaussianReal_zero_var,dirac_withDensity]
    have hew : forwardSchemeWeight s β t j x x = 1 := by
      unfold forwardSchemeWeight
      change ENNReal.ofReal (Real.exp (_*(parisiPotential β _ (b,x)-parisiPotential β _ (a,x)))) = 1
      simp only [he,sub_self,mul_zero,Real.exp_zero,ENNReal.ofReal_one]
    rw [hew,one_smul]
  · have hpos : 0 < b-a := tsub_pos_iff_lt.mpr (lt_of_le_of_ne hab he)
    have hc : ∀ r ∈ Ico (a:ℝ) ((a:ℝ)+(b-a:ℝ≥0)),
        parisiCDF (parisiSchemeMeasure s) r = forwardSchemeMass s j := by
      rw [← NNReal.coe_add, add_tsub_cancel_of_le hab]
      exact fun r hr => parisiCDF_forwardScheme_cell s t ht j hr
    change parisiConstantMassKernel β (parisiSchemeMeasure s) a (b-a) _ x = _
    rw [parisiConstantMassKernel_apply_actual β hβ _ a (b-a) hpos hab1 _ hc x, hvar]
    congr 1
    funext y
    unfold forwardSchemeWeight
    rw [← NNReal.coe_add,add_tsub_cancel_of_le hab]

theorem scaledBrownian_historyLaw (β : ℝ) (T : ℕ → ℝ≥0) (hT : Monotone T) (n : ℕ) :
    canonicalBrownianMeasure.map
      (historySample (fun t sample => β*canonicalBrownian t sample) T n) =
    finiteHistoryLaw (canonicalBrownianMeasure.map (fun sample => β*canonicalBrownian (T 0) sample))
      (fun j => gaussianStateKernel (β^2*((T (j+1):ℝ)-T j)).toNNReal) n := by
  have hXg (r : ℝ≥0) : Measurable (fun sample => β*canonicalBrownian r sample) :=
    (measurable_canonicalBrownian r).const_mul β
  have hB : StronglyAdapted canonicalBrownianFiltration canonicalBrownian :=
    Filtration.stronglyAdapted_natural (fun r => (measurable_canonicalBrownian r).stronglyMeasurable)
  induction n with
  | zero =>
    rw [finiteHistoryLaw,Measure.map_map (by fun_prop) (hXg _)]
    congr 1
    funext sample i
    have hi : i = 0 := Fin.ext (by have := i.isLt;omega)
    simp only [historySample,Function.comp_def,hi,Fin.val_zero]
  | succ n ih =>
    have hY : Measurable[canonicalBrownianFiltration (T n)]
        (historySample (fun t sample => β*canonicalBrownian t sample) T n) := by
      letI : MeasurableSpace BrownianSample := canonicalBrownianFiltration (T n)
      apply Measurable.of_eval
      intro i
      have hm : Measurable[canonicalBrownianFiltration (T i)] (canonicalBrownian (T i)) :=
        (hB (T i)).measurable
      exact (hm.mono (canonicalBrownianFiltration.mono
        (hT (show (i:ℕ) ≤ n by omega))) le_rfl).const_mul β
    have hj := scaledBrownian_joint_transitionLaw β (T n) (T (n+1)) (hT (Nat.le_succ n))
      (historySample (fun t sample => β*canonicalBrownian t sample) T n) hY
      (fun p : FiniteHistory n => p (Fin.last n)) (measurable_pi_apply _) (fun _ => rfl)
    change canonicalBrownianMeasure.map
      (historySample (fun t sample => β*canonicalBrownian t sample) T (n+1)) =
      ((_ ⊗ₘ _).map (historySplit n).symm)
    rw [← ih,← hj,Measure.map_map (historySplit n).symm.measurable
      ((measurable_historySample _ hXg T n).prodMk (hXg _))]
    congr 1
    funext sample
    apply (historySplit n).injective
    simp only [MeasurableEquiv.apply_symm_apply,historySplit_apply,historySample,
      Fin.val_castSucc,Fin.val_last,Function.comp_def]
    rfl

/-- Every finite stopped optimal-state tuple is an actual density tilt of the
corresponding scaled Brownian tuple, with the exact endpoint potentials. -/
theorem selectedState_history_eq_tiltedBrownian {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (n : ℕ) :
    canonicalBrownianMeasure.map
      (historySample (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s))
        (forwardSchemeTime s t) n) =
    (canonicalBrownianMeasure.map
      (historySample (fun r sample => β*canonicalBrownian r sample)
        (forwardSchemeTime s t) n)).withDensity
      (finiteHistoryDensity (forwardSchemeWeight s β t) n) := by
  rw [selectedState_forwardScheme_historyLaw s β 0 hβ t ht n,
    scaledBrownian_historyLaw β (forwardSchemeTime s t) (forwardSchemeTime_monotone s t) n]
  have hi : canonicalBrownianMeasure.map
      (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) 0) =
      canonicalBrownianMeasure.map (fun sample => β*canonicalBrownian
        (forwardSchemeTime s t 0) sample) := by
    congr 1
    funext sample
    simp only [forwardSchemeTime_zero,canonicalBrownian_zero,mul_zero,selectedParisiItoState]
    exact canonicalParisiItoState_zero β 0 _ _ _ _ _ sample
  rw [hi]
  exact finiteHistoryLaw_withDensity _ (forwardGaussianKernel s β t)
    (forwardSchemeKernel s β t) (fun _ => inferInstance)
    (isMarkovKernel_forwardSchemeKernel s β t ht) (forwardSchemeWeight s β t)
    (measurable_forwardSchemeWeight s β t)
    (forwardSchemeKernel_eq_withDensity s β hβ t ht) n

end FRSB
