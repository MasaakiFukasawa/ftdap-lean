import BoundedVariationGains

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V]

/-- Times of oversized active trades, with the horizon always included. -/
noncomputable def PriceJumpModel.oversizedTimes
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) : Finset NNReal :=
  insert T (((M.active ω).filter (fun k => n < ‖H (M.times k ω, ω)‖)).image (fun k => M.times k ω))

/-- First oversized trade time, capped at the horizon. -/
noncomputable def PriceJumpModel.firstOversizedTrade
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) : NNReal :=
  (M.oversizedTimes H n ω).min' (Finset.insert_nonempty _ _)

/-- The first oversized trade event is an explicit union of stopped-mark events. -/
theorem PriceJumpModel.firstOversizedTrade_le_iff
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) (t : NNReal) :
    M.firstOversizedTrade H n ω ≤ t ↔ T ≤ t ∨
      ∃ k ∈ M.active ω, n < ‖H (M.times k ω, ω)‖ ∧ M.times k ω ≤ t := by
  classical
  constructor
  · intro ht
    have hm := Finset.min'_mem (M.oversizedTimes H n ω) (Finset.insert_nonempty _ _)
    rcases Finset.mem_insert.mp hm with he | he
    · exact Or.inl (he ▸ ht)
    · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp he
      obtain ⟨hk, hbig⟩ := Finset.mem_filter.mp hk
      exact Or.inr ⟨k, hk, hbig, heq ▸ ht⟩
  · rintro (hT | ⟨k, hk, hbig, hkt⟩)
    · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans hT
    · apply le_trans (Finset.min'_le _ _ ?_) hkt
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hbig⟩, rfl⟩)

/-- Oversized predictable holdings are known at their jump times, so the first
oversized trade is a genuine stopping time. -/
theorem PriceJumpModel.firstOversizedTrade_stopping [BorelSpace V] [SecondCountableTopology V]
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H) (n : ℝ) :
    IsStoppingTime 𝓕 (fun ω => (M.firstOversizedTrade H n ω : WithTop NNReal)) := by
  intro t
  have hm : ∀ k, MeasurableSet[𝓕 t]
      {ω | k ∈ M.active ω ∧ n < ‖H (M.times k ω, ω)‖ ∧ M.times k ω ≤ t} := by
    intro k
    have hh := predictable_portfolio_stopped_measurable 𝓕 (M.times k) (M.stopping k) H hH
    have hbad : MeasurableSet[(M.stopping k).measurableSpace]
        {ω | n < ‖H (M.times k ω, ω)‖} := by
      let : MeasurableSpace Ω := (M.stopping k).measurableSpace
      exact hh.norm measurableSet_Ioi
    have he : MeasurableSet[(M.stopping k).measurableSpace]
        {ω | k ∈ M.active ω ∧ n < ‖H (M.times k ω, ω)‖} :=
      (M.measurable_active k).inter hbad
    have hcut := ((M.stopping k).measurableSet _).mp he |>.2 t
    convert hcut using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, and_assoc]
  have he : {ω | (M.firstOversizedTrade H n ω : WithTop NNReal) ≤ t} =
      {ω | T ≤ t} ∪ ⋃ k, {ω | k ∈ M.active ω ∧ n < ‖H (M.times k ω, ω)‖ ∧ M.times k ω ≤ t} := by
    ext ω
    simp only [WithTop.coe_le_coe, M.firstOversizedTrade_le_iff, mem_union,
      mem_ofPred_eq, mem_iUnion]
  rw [he]
  exact (MeasurableSet.const (T ≤ t)).union (MeasurableSet.iUnion hm)

/-- Every genuinely oversized jump occurs at or after the first oversized time. -/
theorem PriceJumpModel.firstOversizedTrade_le_jump
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) (k : ℕ) (hk : k ∈ M.active ω)
    (hbig : n < ‖H (M.times k ω, ω)‖) : M.firstOversizedTrade H n ω ≤ M.times k ω :=
  (M.firstOversizedTrade_le_iff H n ω _).mpr (Or.inr ⟨k, hk, hbig, le_rfl⟩)

/-- Before the first oversized trade, every active holding is below threshold. -/
theorem PriceJumpModel.holdings_small_before_first
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) (k : ℕ) (hk : k ∈ M.active ω)
    (ht : M.times k ω < M.firstOversizedTrade H n ω) : ‖H (M.times k ω, ω)‖ ≤ n := by
  apply le_of_not_gt
  intro hbig
  exact (not_lt_of_ge (M.firstOversizedTrade_le_jump H n ω k hk hbig)) ht

/-- The first oversized time is the horizon or an attained oversized jump. -/
theorem PriceJumpModel.firstOversizedTrade_spec
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) :
    M.firstOversizedTrade H n ω ≤ T ∧
      (M.firstOversizedTrade H n ω = T ∨ ∃ k ∈ M.active ω,
        n < ‖H (M.times k ω, ω)‖ ∧ M.times k ω = M.firstOversizedTrade H n ω) := by
  have hT := (M.firstOversizedTrade_le_iff H n ω T).mpr (Or.inl le_rfl)
  refine ⟨hT, ?_⟩
  rcases (M.firstOversizedTrade_le_iff H n ω _).mp le_rfl with hle | ⟨k, hk, hb, hkt⟩
  · exact Or.inl (le_antisymm hT hle)
  · exact Or.inr ⟨k, hk, hb, le_antisymm hkt (M.firstOversizedTrade_le_jump H n ω k hk hb)⟩

#print axioms PriceJumpModel.holdings_small_before_first
#print axioms PriceJumpModel.firstOversizedTrade_spec
#print axioms PriceJumpModel.firstOversizedTrade_le_iff
#print axioms PriceJumpModel.firstOversizedTrade_stopping
#print axioms PriceJumpModel.firstOversizedTrade_le_jump
end FTDAP
