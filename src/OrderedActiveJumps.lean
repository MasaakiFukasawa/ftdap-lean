import ExitRepresentation

open MeasureTheory Set Filter Function
open scoped Topology
namespace FTDAP

/-- Strict advances of a monotone sequence have distinct arrival times. -/
theorem active_arrivals_strictMonoOn (τ : ℕ → ℝ) (hmono : Monotone τ)
    (J : Set ℕ) (hactive : ∀ k ∈ J, τ k < τ (k+1)) :
    StrictMonoOn (fun k => τ (k+1)) J := by
  intro k _hk l hl hkl
  exact lt_of_le_of_lt (hmono (Nat.succ_le_of_lt hkl)) (hactive l hl)

variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The same constructed finite jump set simultaneously gives measurable marks,
ordered positive arrival times, and the price representation on the horizon. -/
theorem constructed_jump_data (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    [𝓕.IsRightContinuous] (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t)) (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (hfinite : ∀ ω, (Set.range (fun t => S t ω)).Finite) (a T : ℝ) (ha : a ≤ T) :
    let τ := priceExitSequence S a T
    let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
    ∃ jumps : Ω → Finset ℕ,
      (∀ k, ∃ hτ : IsStoppingTime 𝓕 (fun ω => (τ (k+1) ω : WithTop ℝ)),
        Measurable[hτ.measurableSpace] (Δ k) ∧
        MeasurableSet[hτ.measurableSpace] {ω | k ∈ jumps ω}) ∧
      (∀ ω, StrictMonoOn (fun k => τ (k+1) ω) (jumps ω : Set ℕ)) ∧
      (∀ ω k, k ∈ jumps ω → a < τ (k+1) ω ∧ τ (k+1) ω ≤ T ∧ Δ k ω ≠ 0) ∧
      ∀ ω t, t ∈ Icc a T → S t ω - S a ω =
        ∑ k ∈ jumps ω, if τ (k+1) ω ≤ t then Δ k ω else 0 := by
  classical
  let τ := priceExitSequence S a T
  let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
  obtain ⟨jumps, hmem, hmeas⟩ := exists_measurable_active_jumps 𝓕 S hadapt hcad hfinite a T ha
  have hb : ∀ ω n, a ≤ τ n ω ∧ τ n ω ≤ T := by
    intro ω n
    have h := exit_sequence_bounds (fun t => S t ω) (hcad ω).isRightContinuous
      (hfinite ω) a T ha n
    simpa only [τ, price_exit_sequence_eq] using (And.intro h.1 h.2.1)
  have hmono : ∀ ω, Monotone (fun n => τ n ω) := by
    intro ω
    apply monotone_nat_of_le_succ
    intro n
    have h := next_exit_properties (fun t => S t ω) (hcad ω).isRightContinuous
      (hfinite ω) _ T (hb ω n).2
    simpa only [τ, price_exit_sequence_eq, exitSequence] using h.1
  refine ⟨jumps, hmeas, ?_, ?_, ?_⟩
  · intro ω
    exact active_arrivals_strictMonoOn _ (hmono ω) _ (fun k hk => ((hmem ω k).mp hk).1)
  · intro ω k hk
    have h := (hmem ω k).mp hk
    exact ⟨lt_of_le_of_lt (hb ω k).1 h.1, (hb ω (k+1)).2, h.2⟩
  · intro ω t ht
    have hm : ∀ k, k ∈ jumps ω ↔
        exitSequence (fun s => S s ω) a T k < exitSequence (fun s => S s ω) a T (k+1) ∧
        S (exitSequence (fun s => S s ω) a T (k+1)) ω -
          leftLim (fun s => S s ω) (exitSequence (fun s => S s ω) a T (k+1)) ≠ 0 := by
      intro k
      simpa only [price_exit_sequence_eq] using hmem ω k
    simpa only [price_exit_sequence_eq] using
      exit_representation_active_set (fun s => S s ω) (hcad ω) (hfinite ω) a T ha
        (jumps ω) hm t ht

#print axioms active_arrivals_strictMonoOn
#print axioms constructed_jump_data
end FTDAP
