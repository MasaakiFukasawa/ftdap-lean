import CompactHorizonPaths

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {V : Type*} [TopologicalSpace V]

/-- Replacing the negative-time part by a constant preserves cadlag paths. -/
theorem cadlag_constant_before_zero (f : ℝ → V) (hf : IsCadlag f) (c : V) :
    IsCadlag (fun t => if t < 0 then c else f t) := by
  refine ⟨?_, ?_⟩
  · intro t
    change Tendsto _ (𝓝[>] t) (𝓝 (if t < 0 then c else f t))
    by_cases ht : t < 0
    · rw [ite_eq_left ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)] with u hu
      exact (ite_eq_left hu).symm
    · rw [ite_eq_right ht]
      apply (hf.isRightContinuous t).congr'
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (ite_eq_right (not_lt.mpr ((le_of_not_gt ht).trans hu.le))).symm
  · intro t
    by_cases ht : t ≤ 0
    · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (ite_eq_left (hu.trans_le ht)).symm
    · obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT t
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (lt_of_not_ge ht))] with u hu
      exact (ite_eq_right (not_lt.mpr hu.le)).symm

variable {Ω : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- Deterministic negative-time values make the compact price extension
adapted even for a filtration indexed by all real numbers. -/
noncomputable def compactPriceExtension (T : NNReal) (S : Icc (0 : ℝ) (T : ℝ) → Ω → V)
    (s₀ : V) : ℝ → Ω → V := fun t ω => if t < 0 then s₀ else S (horizonClamp T t) ω

omit [TopologicalSpace V] [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V] in
/-- The extension agrees with the original price at every horizon time. -/
theorem compactPriceExtension_value (T : NNReal)
    (S : Icc (0 : ℝ) (T : ℝ) → Ω → V) (s₀ : V) (t : Icc (0 : ℝ) (T : ℝ)) :
    compactPriceExtension T S s₀ t.val = S t := by
  have hc : horizonClamp T t.val = t := Subtype.ext (horizonClamp_value T t.val t.property)
  funext ω
  change (if t.val < 0 then s₀ else S (horizonClamp T t.val) ω) = S t ω
  rw [ite_eq_right (not_lt.mpr t.property.1), hc]

omit [TopologicalSpace V] [NormedAddCommGroup V] in
/-- Adapted compact-horizon prices have an adapted real-time extension. -/
theorem compactPriceExtension_adapted (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (T : NNReal) (S : Icc (0 : ℝ) (T : ℝ) → Ω → V) (s₀ : V)
    (ha : ∀ t, Measurable[𝓕 t.val] (S t)) :
    ∀ t, Measurable[𝓕 t] (compactPriceExtension T S s₀ t) := by
  intro t
  change Measurable[𝓕 t] (fun ω => if t < 0 then s₀ else S (horizonClamp T t) ω)
  by_cases ht : t < 0
  · simpa only [ite_eq_left ht] using
      (measurable_const : Measurable[𝓕 t] (fun _ : Ω => s₀))
  · have hle : (horizonClamp T t : ℝ) ≤ t := by
      change min (max t 0) (T : ℝ) ≤ t
      rw [max_eq_left (le_of_not_gt ht)]
      exact min_le_left _ _
    simpa only [ite_eq_right ht] using
      (ha (horizonClamp T t)).mono (𝓕.mono hle) le_rfl

#print axioms cadlag_constant_before_zero
#print axioms compactPriceExtension_value
#print axioms compactPriceExtension_adapted
end FTDAP
