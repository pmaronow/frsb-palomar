module

public import FRSB.ForwardLeftAtoms
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! Sorted actual support nodes, stopped at an arbitrary positive
observation time. Every consecutive open cell has exactly zero mass. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

/-- Include zero and the observation endpoint; retain every support atom
strictly before the endpoint. -/
def forwardSupportNodes (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : Finset Overlap :=
  insert overlapZero (insert ⟨s,hs.1.le,hs.2⟩ (hμ.toFinset.filter fun t => (t : ℝ) ≤ s))

lemma forwardSupportNodes_card_pos (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : 0 < (forwardSupportNodes μ hμ s hs).card :=
  Finset.card_pos.mpr ⟨overlapZero,by simp [forwardSupportNodes]⟩

def forwardSupportNode (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    Fin (forwardSupportNodes μ hμ s hs).card ↪o Overlap :=
  (forwardSupportNodes μ hμ s hs).orderEmbOfFin rfl

lemma forwardSupportNode_le (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (i : Fin (forwardSupportNodes μ hμ s hs).card) :
    (forwardSupportNode μ hμ s hs i : ℝ) ≤ s := by
  have hm : forwardSupportNode μ hμ s hs i ∈ forwardSupportNodes μ hμ s hs :=
    Finset.orderEmbOfFin_mem _ rfl i
  simp only [forwardSupportNodes, Finset.mem_insert, Finset.mem_filter] at hm
  rcases hm with h | h | h
  · have hv := congrArg Subtype.val h
    change (forwardSupportNode μ hμ s hs i).val ≤ s
    exact hv.le.trans hs.1.le
  · have hv := congrArg Subtype.val h
    change (forwardSupportNode μ hμ s hs i).val ≤ s
    exact hv.le
  · exact h.2

lemma forwardSupportNode_zero (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    forwardSupportNode μ hμ s hs ⟨0,forwardSupportNodes_card_pos μ hμ s hs⟩ = overlapZero := by
  let e := (forwardSupportNodes μ hμ s hs).orderIsoOfFin rfl
  let j := e.symm ⟨overlapZero,by simp [forwardSupportNodes]⟩
  have hj : forwardSupportNode μ hμ s hs j = overlapZero := by
    change (e (e.symm _)).val = _
    simp
  apply Subtype.ext
  apply le_antisymm
  · have he := (forwardSupportNode μ hμ s hs).monotone
      (show (⟨0,forwardSupportNodes_card_pos μ hμ s hs⟩ : Fin _) ≤ j from Nat.zero_le _)
    rw [hj] at he
    exact he
  · exact (forwardSupportNode μ hμ s hs _).property.1

lemma forwardSupportNode_last (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    forwardSupportNode μ hμ s hs
      ⟨(forwardSupportNodes μ hμ s hs).card - 1,
        Nat.sub_lt (forwardSupportNodes_card_pos μ hμ s hs) (by omega)⟩ = ⟨s,hs.1.le,hs.2⟩ := by
  let e := (forwardSupportNodes μ hμ s hs).orderIsoOfFin rfl
  let j := e.symm ⟨⟨s,hs.1.le,hs.2⟩,by simp [forwardSupportNodes]⟩
  have hj : forwardSupportNode μ hμ s hs j = ⟨s,hs.1.le,hs.2⟩ := by
    change (e (e.symm _)).val = _
    simp
  apply Subtype.ext
  apply le_antisymm
  · exact forwardSupportNode_le μ hμ s hs _
  · have hjle : j.val ≤ (forwardSupportNodes μ hμ s hs).card - 1 := by omega
    have he := (forwardSupportNode μ hμ s hs).monotone
      (show j ≤ (⟨(forwardSupportNodes μ hμ s hs).card - 1,
        Nat.sub_lt (forwardSupportNodes_card_pos μ hμ s hs) (by omega)⟩ : Fin _) from hjle)
    rw [hj] at he
    exact he

lemma forwardSupportNode_pos (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (i : Fin (forwardSupportNodes μ hμ s hs).card)
    (hi : 0 < (i : ℕ)) : 0 < (forwardSupportNode μ hμ s hs i : ℝ) := by
  have hh := (forwardSupportNode μ hμ s hs).strictMono
    (show (⟨0,forwardSupportNodes_card_pos μ hμ s hs⟩ : Fin _) < i from hi)
  rw [forwardSupportNode_zero μ hμ s hs] at hh
  exact hh

lemma forwardSupportNode_mem_Ioc (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (i : Fin (forwardSupportNodes μ hμ s hs).card)
    (hi : 0 < (i : ℕ)) : (forwardSupportNode μ hμ s hs i : ℝ) ∈ Ioc (0 : ℝ) 1 :=
  ⟨forwardSupportNode_pos μ hμ s hs i hi,
    (forwardSupportNode_le μ hμ s hs i).trans hs.2⟩

/-- Every support point up to the observation endpoint is one of the
concrete sorted nodes, including the zero atom and a terminal atom. -/
lemma mem_forwardSupportNodes_of_support (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (t : Overlap) (ht : t ∈ (μ : Measure Overlap).support)
    (hts : (t : ℝ) ≤ s) : t ∈ forwardSupportNodes μ hμ s hs := by
  simp only [forwardSupportNodes, Finset.mem_insert, Finset.mem_filter]
  exact Or.inr (Or.inr ⟨hμ.mem_toFinset.mpr ht,hts⟩)

lemma forwardSupportNode_cell_no_support (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (i : ℕ) (hi : i + 1 < (forwardSupportNodes μ hμ s hs).card)
    (t : Overlap) (ht : (forwardSupportNode μ hμ s hs ⟨i,by omega⟩ : ℝ) < t)
    (ht' : (t : ℝ) < forwardSupportNode μ hμ s hs ⟨i+1,hi⟩) :
    t ∉ (μ : Measure Overlap).support := by
  intro hsup
  let e := (forwardSupportNodes μ hμ s hs).orderIsoOfFin rfl
  have hmem : t ∈ forwardSupportNodes μ hμ s hs :=
    mem_forwardSupportNodes_of_support μ hμ s hs t hsup
      (ht'.le.trans (forwardSupportNode_le μ hμ s hs _))
  let j := e.symm ⟨t,hmem⟩
  have hj : forwardSupportNode μ hμ s hs j = t := by
    change (e (e.symm _)).val = _
    simp
  have hlow : i < (j : ℕ) := by
    by_contra hn
    have hh := (forwardSupportNode μ hμ s hs).monotone
      (show j ≤ (⟨i,by omega⟩ : Fin _) from le_of_not_gt hn)
    rw [hj] at hh
    exact (not_lt_of_ge hh) ht
  have hhigh : (j : ℕ) < i + 1 := by
    by_contra hn
    have hh := (forwardSupportNode μ hμ s hs).monotone
      (show (⟨i+1,hi⟩ : Fin _) ≤ j from le_of_not_gt hn)
    rw [hj] at hh
    exact (not_lt_of_ge hh) ht'
  omega

lemma forwardSupportNode_cell_zero_mass (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (i : ℕ) (hi : i + 1 < (forwardSupportNodes μ hμ s hs).card) :
    (μ : Measure Overlap) {t : Overlap |
      (forwardSupportNode μ hμ s hs ⟨i,by omega⟩ : ℝ) < t ∧
      (t : ℝ) < forwardSupportNode μ hμ s hs ⟨i+1,hi⟩} = 0 := by
  apply measure_mono_null (fun t ht => forwardSupportNode_cell_no_support μ hμ s hs i hi t ht.1 ht.2)
  exact Measure.measure_compl_support_of_innerRegular

lemma forwardSupportNodes_one_lt_card (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    1 < (forwardSupportNodes μ hμ s hs).card := by
  apply Finset.one_lt_card.mpr
  refine ⟨overlapZero, by simp [forwardSupportNodes], ⟨s,hs.1.le,hs.2⟩,
    by simp [forwardSupportNodes], ?_⟩
  intro he
  have hv := congrArg Subtype.val he
  change 0 = s at hv
  linarith [hs.1]

/-- An open zero-mass interval has a genuinely constant right CDF up to
the terminal point; the initial atom is included and the final atom is excluded. -/
lemma forwardCDF_constant_of_open_mass_zero (μ : ParisiMeasure) (r t : ℝ)
    (hzero : (μ : Measure Overlap) {q : Overlap | r < (q : ℝ) ∧ (q : ℝ) < t} = 0)
    (z : ℝ) (hz : z ∈ Ico r t) : parisiCDF μ z = parisiCDF μ r := by
  have hAE : ∀ᵐ q : Overlap ∂(μ : Measure Overlap), ¬(r < (q : ℝ) ∧ (q : ℝ) < t) :=
    ae_iff.mpr (by simpa only [not_not] using hzero)
  unfold parisiCDF
  congr 1
  apply measure_congr
  filter_upwards [hAE] with q hq
  apply propext
  constructor
  · intro hqz
    exact le_of_not_gt (fun hqr => hq ⟨hqr,hqz.trans_lt hz.2⟩)
  · exact fun hqr => hqr.trans hz.1

lemma forwardLeftMass_eq_cdf_of_open_mass_zero (μ : ParisiMeasure) (r t : ℝ) (hrt : r < t)
    (hzero : (μ : Measure Overlap) {q : Overlap | r < (q : ℝ) ∧ (q : ℝ) < t} = 0) :
    parisiLeftMass μ t = parisiCDF μ r := by
  have hAE : ∀ᵐ q : Overlap ∂(μ : Measure Overlap), ¬(r < (q : ℝ) ∧ (q : ℝ) < t) :=
    ae_iff.mpr (by simpa only [not_not] using hzero)
  unfold parisiCDF parisiLeftMass
  congr 1
  apply measure_congr
  filter_upwards [hAE] with q hq
  apply propext
  constructor
  · intro hqt
    exact le_of_not_gt (fun hqr => hq ⟨hqr,hqt⟩)
  · exact fun hqr => hqr.trans_lt hrt

end FRSB
