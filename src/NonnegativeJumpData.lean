import NonnegativeTime

open MeasureTheory Set Filter Function
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The constructed price jumps have the time type and stopped measurability
required by the predictable trading interface. -/
theorem constructed_nonnegative_jump_data
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (hfinite : ∀ ω, (Set.range (fun t => S t ω)).Finite) (T : NNReal) :
    let τ := priceExitSequence S 0 (T : ℝ)
    let ν := fun k ω => Real.toNNReal (τ (k+1) ω)
    let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
    ∃ jumps : Ω → Finset ℕ,
      (∀ k, ∃ hν : IsStoppingTime (nonnegativeFiltration 𝓕)
          (fun ω => WithTop.some (ν k ω)),
        Measurable[hν.measurableSpace] (Δ k) ∧
        MeasurableSet[hν.measurableSpace] {ω | k ∈ jumps ω}) ∧
      (∀ ω, Set.InjOn (fun k => ν k ω) (jumps ω : Set ℕ)) ∧
      (∀ ω k, k ∈ jumps ω → 0 < ν k ω ∧ ν k ω ≤ T ∧ Δ k ω ≠ 0) ∧
      ∀ (ω : Ω) (t : NNReal), t ≤ T → S (t : ℝ) ω - S 0 ω =
        ∑ k ∈ jumps ω, if ν k ω ≤ t then Δ k ω else 0 := by
  classical
  let τ := priceExitSequence S 0 (T : ℝ)
  let ν := fun k ω => Real.toNNReal (τ (k+1) ω)
  let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
  obtain ⟨jumps, hmeas, horder, hbounds, hrep⟩ :=
    constructed_jump_data 𝓕 S hadapt hcad hfinite 0 (T : ℝ) T.2
  have hval : ∀ k ω, (ν k ω : ℝ) = τ (k+1) ω := by
    intro k ω
    apply Real.coe_toNNReal
    have h := exit_sequence_bounds (fun t => S t ω) (hcad ω).isRightContinuous
      (hfinite ω) 0 (T : ℝ) T.2 (k+1)
    simpa only [τ, price_exit_sequence_eq] using h.1
  refine ⟨jumps, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨hτ, hΔ, hJ⟩ := hmeas k
    refine ⟨nonnegative_stopping_time 𝓕 (τ (k+1)) hτ, ?_, ?_⟩
    · exact hΔ.mono (nonnegative_stopped_information 𝓕 (τ (k+1)) hτ) le_rfl
    · exact (nonnegative_stopped_information 𝓕 (τ (k+1)) hτ) _ hJ
  · intro ω k hk l hl heq
    apply (horder ω).injOn hk hl
    have he := congrArg (fun x : NNReal => (x : ℝ)) heq
    change (ν k ω : ℝ) = (ν l ω : ℝ) at he
    rw [hval k ω, hval l ω] at he
    exact he
  · intro ω k hk
    obtain ⟨hp, hb, hd⟩ := hbounds ω k hk
    refine ⟨?_, ?_, hd⟩
    · apply NNReal.coe_lt_coe.mp
      change (0 : ℝ) < (ν k ω : ℝ)
      rw [hval k ω]
      exact hp
    · apply NNReal.coe_le_coe.mp
      change (ν k ω : ℝ) ≤ (T : ℝ)
      rw [hval k ω]
      exact hb
  · intro ω t ht
    have hr := hrep ω (t : ℝ) ⟨t.2, ht⟩
    simpa only [Real.toNNReal_le_iff_le_coe] using hr

#print axioms constructed_nonnegative_jump_data
end FTDAP
