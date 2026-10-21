import FirstOversizedTrade

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Clip oversized holdings and stop at their first occurrence, omitting the
oversized jump itself. -/
noncomputable def PriceJumpModel.truncatedHoldings
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) : NNReal × Ω → V :=
  stoppedStrategy (fun p => if ‖H p‖ ≤ n then H p else 0) (M.firstOversizedTrade H n)

omit [InnerProductSpace ℝ V] in
/-- The truncation is predictable and globally bounded. -/
theorem PriceJumpModel.truncatedHoldings_predictable_bound
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H) (n : ℝ) (hn : 0 ≤ n) :
    Measurable[𝓕.predictable] (M.truncatedHoldings H n) ∧ ∀ p, ‖M.truncatedHoldings H n p‖ ≤ n := by
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  have hclip : Measurable[𝓕.predictable] (fun p => if ‖H p‖ ≤ n then H p else 0) :=
    hH.ite (hH.norm measurableSet_Iic) measurable_const
  refine ⟨stopped_strategy_predictable 𝓕 _ hclip _ (M.firstOversizedTrade_stopping H hH n), ?_⟩
  intro p
  change ‖if p.1 ≤ M.firstOversizedTrade H n p.2 then (if ‖H p‖ ≤ n then H p else 0) else 0‖ ≤ n
  split_ifs with ht hnorm
  · exact hnorm
  · simpa only [norm_zero] using hn
  · simpa only [norm_zero] using hn

omit [BorelSpace V] [SecondCountableTopology V] in
/-- If every active holding is small, the truncation preserves every gain. -/
theorem PriceJumpModel.truncated_gain_when_all_small
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω)
    (hsmall : ∀ k ∈ M.active ω, ‖H (M.times k ω, ω)‖ ≤ n) :
    ∀ t, finiteJumpGain M.active M.times M.marks (M.truncatedHoldings H n) t ω =
      finiteJumpGain M.active M.times M.marks H t ω := by
  have hη : M.firstOversizedTrade H n ω = T := by
    apply le_antisymm (M.firstOversizedTrade_spec H n ω).1
    rcases (M.firstOversizedTrade_le_iff H n ω _).mp le_rfl with h | ⟨k, hk, hb, _⟩
    · exact h
    · exact (not_lt_of_ge (hsmall k hk) hb).elim
  intro t
  apply Finset.sum_congr rfl
  intro k hk
  simp only [truncatedHoldings, stoppedStrategy, hη,
    ite_eq_left (M.bounds ω k hk).2.1, ite_eq_left (hsmall k hk)]

omit [BorelSpace V] [SecondCountableTopology V] in
/-- At a first oversized jump, truncation agrees with the old gain before the
jump and freezes at its left limit from that time onward. -/
theorem PriceJumpModel.truncated_gain_at_first_bad
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n : ℝ) (ω : Ω) (k : ℕ) (hk : k ∈ M.active ω)
    (hbig : n < ‖H (M.times k ω, ω)‖)
    (hkη : M.times k ω = M.firstOversizedTrade H n ω) (t : NNReal) :
    finiteJumpGain M.active M.times M.marks (M.truncatedHoldings H n) t ω =
      if t < M.firstOversizedTrade H n ω then finiteJumpGain M.active M.times M.marks H t ω
      else preJumpGain M.active M.times M.marks H (M.firstOversizedTrade H n ω) ω := by
  classical
  by_cases ht : t < (M.firstOversizedTrade H n ω)
  · rw [ite_eq_left ht]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjt : M.times j ω ≤ t
    · have hjη := hjt.trans_lt ht
      have hsmall := M.holdings_small_before_first H n ω j hj hjη
      simp only [ite_eq_left hjt, truncatedHoldings, stoppedStrategy, ite_eq_left hjη.le,
        ite_eq_left hsmall]
    · simp only [ite_eq_right hjt]
  · rw [ite_eq_right ht]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjη : M.times j ω < (M.firstOversizedTrade H n ω)
    · have hsmall := M.holdings_small_before_first H n ω j hj hjη
      have hjt := hjη.le.trans (le_of_not_gt ht)
      simp only [ite_eq_left hjt, ite_eq_left hjη, truncatedHoldings, stoppedStrategy,
        ite_eq_left hjη.le, ite_eq_left hsmall]
    · have hzero : M.truncatedHoldings H n (M.times j ω, ω) = 0 := by
        by_cases heq : M.times j ω = (M.firstOversizedTrade H n ω)
        · have hjk : j = k := M.injective_times ω hj hk (heq.trans hkη.symm)
          subst j
          simp only [truncatedHoldings, stoppedStrategy, ite_eq_left (show M.times k ω ≤ (M.firstOversizedTrade H n ω) from hkη.le),
            ite_eq_right (not_le_of_gt hbig)]
        · have hgt : (M.firstOversizedTrade H n ω) < M.times j ω := lt_of_le_of_ne (le_of_not_gt hjη) (Ne.symm heq)
          simp only [truncatedHoldings, stoppedStrategy, ite_eq_right (not_le_of_gt hgt)]
      change (if M.times j ω ≤ t then inner ℝ (M.truncatedHoldings H n (M.times j ω, ω)) (M.marks j ω) else 0) = _
      rw [hzero]
      simp only [inner_zero_left, ite_self, ite_eq_right hjη]

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Truncation retains the original all-time lower bound by freezing at the
pre-jump gain when it encounters the first oversized holding. -/
theorem PriceJumpModel.truncated_gain_lower_bound
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (n a : ℝ) (ω : Ω)
    (hbound : ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks H t ω) :
    ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks (M.truncatedHoldings H n) t ω := by
  classical
  by_cases hbad : ∃ k ∈ M.active ω, n < ‖H (M.times k ω, ω)‖ ∧
      M.times k ω = M.firstOversizedTrade H n ω
  · obtain ⟨k, hk, hb, hkη⟩ := hbad
    intro t ht
    rw [M.truncated_gain_at_first_bad H n ω k hk hb hkη t]
    split_ifs with hbefore
    · exact hbound t ht
    · have hp : 0 < M.firstOversizedTrade H n ω := hkη ▸ (M.bounds ω k hk).1
      have : NeBot (𝓝[<] (M.firstOversizedTrade H n ω)) := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
      exact pre_jump_gain_lower_bound M.active M.times M.marks H _ T ω a
        (M.firstOversizedTrade_spec H n ω).1 hbound
  · have hη : M.firstOversizedTrade H n ω = T :=
      (M.firstOversizedTrade_spec H n ω).2.resolve_right hbad
    have hsmall : ∀ k ∈ M.active ω, ‖H (M.times k ω, ω)‖ ≤ n := by
      intro k hk
      apply le_of_not_gt
      intro hb
      have heq : M.times k ω = M.firstOversizedTrade H n ω := le_antisymm
        (by rw [hη]; exact (M.bounds ω k hk).2.1) (M.firstOversizedTrade_le_jump H n ω k hk hb)
      exact hbad ⟨k, hk, hb, heq⟩
    intro t ht
    rw [M.truncated_gain_when_all_small H n ω hsmall t]
    exact hbound t ht

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Each finite path eventually has no oversized active holding at all. -/
theorem PriceJumpModel.truncated_gains_eventually_equal
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (ω : Ω) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t, finiteJumpGain M.active M.times M.marks (M.truncatedHoldings H (n : ℝ)) t ω =
      finiteJumpGain M.active M.times M.marks H t ω := by
  have hb := ((M.active ω).finite_toSet.image (fun k => ‖H (M.times k ω, ω)‖)).bddAbove
  obtain ⟨B, hB⟩ := hb
  obtain ⟨N, hN⟩ := exists_nat_ge B
  refine ⟨N, ?_⟩
  intro n hn t
  apply M.truncated_gain_when_all_small H (n : ℝ) ω
  intro k hk
  exact (hB ⟨k, hk, rfl⟩).trans (hN.trans (Nat.cast_le.mpr hn))

#print axioms PriceJumpModel.truncated_gain_lower_bound
#print axioms PriceJumpModel.truncated_gains_eventually_equal
#print axioms PriceJumpModel.truncatedHoldings_predictable_bound
#print axioms PriceJumpModel.truncated_gain_when_all_small
#print axioms PriceJumpModel.truncated_gain_at_first_bad
end FTDAP
