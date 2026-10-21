import ReductionFromPrices
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open MeasureTheory Set
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The generating rectangles of the predictable sigma-algebra on nonnegative time. -/
def predictableRectangles (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›) : Set (Set (NNReal × Ω)) :=
  {s | ∃ A, MeasurableSet[𝓕 0] A ∧ s = {(0 : NNReal)} ×ˢ A} ∪
  {s | ∃ t A, MeasurableSet[𝓕 t] A ∧ s = Ioi t ×ˢ A}

/-- Predictable generating rectangles form a pi-system. -/
theorem predictable_rectangles_pi (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›) :
    IsPiSystem (predictableRectangles 𝓕) := by
  intro s hs t ht hne
  rcases hs with ⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩ <;>
    rcases ht with ⟨B, hB, rfl⟩ | ⟨j, B, hB, rfl⟩
  · exact Or.inl ⟨A ∩ B, hA.inter hB, by rw [prod_inter_prod, inter_self]⟩
  · obtain ⟨p, hp, hq⟩ := hne
    have hz : p.1 = 0 := hp.1
    have hl : j < p.1 := hq.1
    rw [hz] at hl
    exact (not_lt_of_ge (show (0 : NNReal) ≤ j from bot_le) hl).elim
  · obtain ⟨p, hp, hq⟩ := hne
    have hz : p.1 = 0 := hq.1
    have hl : i < p.1 := hp.1
    rw [hz] at hl
    exact (not_lt_of_ge (show (0 : NNReal) ≤ i from bot_le) hl).elim
  · have ha : MeasurableSet[𝓕 (i ⊔ j)] A := (𝓕.mono le_sup_left) A hA
    have hb : MeasurableSet[𝓕 (i ⊔ j)] B := (𝓕.mono le_sup_right) B hB
    refine Or.inr ⟨i ⊔ j, A ∩ B, ha.inter hb, ?_⟩
    rw [prod_inter_prod, Ioi_inter_Ioi]

/-- Equality on predictable rectangles identifies finite measures on the full
predictable sigma-algebra; no monotone-class assertion is assumed. -/
theorem predictable_measure_ext (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (μ ν : @Measure (NNReal × Ω) 𝓕.predictable) [IsFiniteMeasure μ]
    (hzero : ∀ A, MeasurableSet[𝓕 0] A → μ ({(0 : NNReal)} ×ˢ A) = ν ({(0 : NNReal)} ×ˢ A))
    (hrect : ∀ t A, MeasurableSet[𝓕 t] A → μ (Ioi t ×ˢ A) = ν (Ioi t ×ˢ A)) : μ = ν := by
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  have hgen : 𝓕.predictable = MeasurableSpace.generateFrom (predictableRectangles 𝓕) := rfl
  have hu : ({(0 : NNReal)} ×ˢ (univ : Set Ω)) ∪ (Ioi (0 : NNReal) ×ˢ (univ : Set Ω)) = univ := by
    ext p
    simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true, mem_Ioi,
      iff_true]
    exact (eq_or_lt_of_le (show (0 : NNReal) ≤ p.1 from bot_le)).imp Eq.symm id
  have hd : Disjoint ({(0 : NNReal)} ×ˢ (univ : Set Ω)) (Ioi (0 : NNReal) ×ˢ (univ : Set Ω)) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    have hz : p.1 = 0 := hp.1
    have hl : (0 : NNReal) < p.1 := hq.1
    rw [hz] at hl
    exact lt_irrefl _ hl
  have hmu : μ univ = ν univ := by
    rw [← hu, measure_union hd (measurableSet_predictable_Ioi_prod MeasurableSet.univ),
      measure_union hd (measurableSet_predictable_Ioi_prod MeasurableSet.univ),
      hzero univ MeasurableSet.univ, hrect 0 univ MeasurableSet.univ]
  apply MeasureTheory.ext_of_generate_finite (predictableRectangles 𝓕) hgen
    (predictable_rectangles_pi 𝓕) _ hmu
  intro s hs
  rcases hs with ⟨A, hA, rfl⟩ | ⟨t, A, hA, rfl⟩
  · exact hzero A hA
  · exact hrect t A hA

#print axioms predictable_rectangles_pi
#print axioms predictable_measure_ext
end FTDAP
