import ContinuousStoppedMartingale

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- The first active jump whose enumeration index is at least `n`, capped at T. -/
noncomputable def PriceJumpModel.tailJumpStop
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (n : ℕ) (ω : Ω) : NNReal :=
  (insert T (((M.active ω).filter (fun k => n ≤ k)).image (fun k => M.times k ω))).min'
    (Finset.insert_nonempty _ _)

theorem PriceJumpModel.tailJumpStop_le_iff
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (n : ℕ) (ω : Ω) (t : NNReal) :
    M.tailJumpStop n ω ≤ t ↔ T ≤ t ∨
      ∃ k ∈ M.active ω, n ≤ k ∧ M.times k ω ≤ t := by
  constructor
  · intro ht
    have hm := Finset.min'_mem
      (insert T (((M.active ω).filter (fun k => n ≤ k)).image (fun k => M.times k ω)))
      (Finset.insert_nonempty _ _)
    rcases Finset.mem_insert.mp hm with he | he
    · exact Or.inl (he ▸ ht)
    · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp he
      obtain ⟨hk, hbig⟩ := Finset.mem_filter.mp hk
      exact Or.inr ⟨k, hk, hbig, heq ▸ ht⟩
  · rintro (hT | ⟨k, hk, hbig, hkt⟩)
    · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans hT
    · apply le_trans (Finset.min'_le _ _ ?_) hkt
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hbig⟩, rfl⟩)

theorem PriceJumpModel.tailJumpStop_stopping
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T) (n : ℕ) :
    IsStoppingTime 𝓕 (fun ω => (M.tailJumpStop n ω : WithTop NNReal)) := by
  intro t
  have hm : ∀ k, MeasurableSet[𝓕 t]
      {ω | k ∈ M.active ω ∧ n ≤ k ∧ M.times k ω ≤ t} := by
    intro k
    have he := (M.measurable_active k).inter (MeasurableSet.const (n ≤ k))
    have hcut := ((M.stopping k).measurableSet _).mp he |>.2 t
    convert hcut using 1
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe, and_assoc]
  have he : {ω | (M.tailJumpStop n ω : WithTop NNReal) ≤ t} =
      {ω | T ≤ t} ∪ ⋃ k, {ω | k ∈ M.active ω ∧ n ≤ k ∧ M.times k ω ≤ t} := by
    ext ω
    simp only [WithTop.coe_le_coe, M.tailJumpStop_le_iff, mem_union,
      mem_ofPred_eq, mem_iUnion]
  rw [he]
  exact (MeasurableSet.const (T ≤ t)).union (MeasurableSet.iUnion hm)

theorem PriceJumpModel.tailJumpStop_le_horizon
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T) (n : ℕ) (ω : Ω) :
    M.tailJumpStop n ω ≤ T := (M.tailJumpStop_le_iff n ω T).mpr (Or.inl le_rfl)

/-- Finite active sets ensure that the index cutoff eventually does nothing. -/
theorem PriceJumpModel.tailJumpStop_eventually_horizon
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T) (ω : Ω) :
    ∀ᶠ n in atTop, M.tailJumpStop n ω = T := by
  obtain ⟨N, hN⟩ := (M.active ω).finite_toSet.bddAbove
  apply eventually_atTop.mpr
  refine ⟨N + 1, fun n hn => le_antisymm (M.tailJumpStop_le_horizon n ω) ?_⟩
  rcases (M.tailJumpStop_le_iff n ω _).mp le_rfl with ht | ⟨k, hk, hnk, _⟩
  · exact ht
  · have hkN := hN hk
    omega

/-- At most one retained jump can have index outside `range n`: it must be the
stopping jump itself, whose time uniquely determines the active index. -/
theorem PriceJumpModel.tailJumpStop_card_bound
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T) (n : ℕ) (ω : Ω) :
    ((M.active ω).filter (fun k => M.times k ω ≤ M.tailJumpStop n ω)).card ≤ n + 1 := by
  let J := (M.active ω).filter (fun k => M.times k ω ≤ M.tailJumpStop n ω)
  have ht : ∀ k ∈ J, n ≤ k → M.times k ω = M.tailJumpStop n ω := by
    intro k hk hnk
    obtain ⟨hk, htime⟩ := Finset.mem_filter.mp hk
    exact le_antisymm htime ((M.tailJumpStop_le_iff n ω _).mpr (Or.inr ⟨k, hk, hnk, le_rfl⟩))
  by_cases hex : ∃ k ∈ J, n ≤ k
  · obtain ⟨k, hk, hnk⟩ := hex
    have hsub : J ⊆ insert k (Finset.range n) := by
      intro l hl
      by_cases hln : l < n
      · exact Finset.mem_insert_of_mem (Finset.mem_range.mpr hln)
      · have hlk : l = k := M.injective_times ω (Finset.mem_filter.mp hl).1
          (Finset.mem_filter.mp hk).1 ((ht l hl (Nat.le_of_not_gt hln)).trans (ht k hk hnk).symm)
        exact Finset.mem_insert.mpr (Or.inl hlk)
    exact (Finset.card_le_card hsub).trans (by simp only [Finset.card_insert_of_notMem
      (show k ∉ Finset.range n by simpa only [Finset.mem_range, not_lt] using hnk), Finset.card_range]; exact le_rfl)
  · have hsub : J ⊆ Finset.range n := by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_not_ge (fun hn => hex ⟨k, hk, hn⟩))
    exact (Finset.card_le_card hsub).trans (by simp only [Finset.card_range]; omega)

#print axioms PriceJumpModel.tailJumpStop_stopping
#print axioms PriceJumpModel.tailJumpStop_eventually_horizon
#print axioms PriceJumpModel.tailJumpStop_card_bound
end FTDAP
