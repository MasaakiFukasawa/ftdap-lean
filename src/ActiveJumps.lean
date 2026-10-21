import StoppedLeftLimits

open MeasureTheory Set Filter Function
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A strict advance and a nonzero increment define a stopping-time measurable
active-jump event. Repeated terminal times are excluded. -/
theorem active_jump_event_measurable (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (σ τ : Ω → ℝ)
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    (hle : ∀ ω, σ ω ≤ τ ω) (Δ : Ω → V) (hΔ : Measurable[hτ.measurableSpace] Δ) :
    MeasurableSet[hτ.measurableSpace] {ω | σ ω < τ ω ∧ Δ ω ≠ 0} := by
  have heq := IsStoppingTime.measurableSet_eq_stopping_time hτ hσ
  have hstrict : MeasurableSet[hτ.measurableSpace] {ω | σ ω < τ ω} := by
    convert heq.compl using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_eq_coe]
    exact ⟨fun h => ne_of_gt h, fun h => lt_of_le_of_ne (hle ω) (Ne.symm h)⟩
  exact hstrict.inter (hΔ (measurableSet_singleton 0)).compl

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Eventually absorbed time sequences have a finite set of active indices. -/
theorem finite_active_indices (τ : ℕ → ℝ) (Δ : ℕ → V) (T : ℝ)
    (hterminal : ∃ N, ∀ k, τ (N+k) = T) :
    {k | τ k < τ (k+1) ∧ Δ k ≠ 0}.Finite := by
  obtain ⟨N, hN⟩ := hterminal
  apply (Finset.finite_toSet (Finset.range N)).subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
  have hnext : τ (N+j+1) = T := by simpa only [Nat.add_assoc] using hN (j+1)
  change τ (N+j) < τ (N+j+1) ∧ Δ (N+j) ≠ 0 at hk
  rw [hN j, hnext] at hk
  exact lt_irrefl T hk.1

/-- The recursive exit construction supplies finite active sets and measurable
increment data, under adapted cadlag finite-range price paths. -/
theorem exists_measurable_active_jumps (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    [𝓕.IsRightContinuous] (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t)) (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (hfinite : ∀ ω, (Set.range (fun t => S t ω)).Finite) (a T : ℝ) (ha : a ≤ T) :
    let τ := priceExitSequence S a T
    let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
    ∃ jumps : Ω → Finset ℕ,
      (∀ ω k, k ∈ jumps ω ↔ τ k ω < τ (k+1) ω ∧ Δ k ω ≠ 0) ∧
      ∀ k, ∃ hτ : IsStoppingTime 𝓕 (fun ω => (τ (k+1) ω : WithTop ℝ)),
        Measurable[hτ.measurableSpace] (Δ k) ∧
        MeasurableSet[hτ.measurableSpace] {ω | k ∈ jumps ω} := by
  classical
  let τ := priceExitSequence S a T
  let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
  have hs := adapted_price_exit_sequence_stopping_times 𝓕 S hadapt
    (fun ω => (hcad ω).isRightContinuous) a T
  have hmon : ∀ ω k, τ k ω ≤ τ (k+1) ω := by
    intro ω k
    have hb := exit_sequence_bounds (fun t => S t ω) (hcad ω).isRightContinuous
      (hfinite ω) a T ha k
    change priceExitSequence S a T k ω ≤ priceExitSequence S a T (k+1) ω
    rw [price_exit_sequence_eq, price_exit_sequence_eq]
    exact (next_exit_properties _ (hcad ω).isRightContinuous (hfinite ω) _ T hb.2.1).1
  have hf : ∀ ω, {k | τ k ω < τ (k+1) ω ∧ Δ k ω ≠ 0}.Finite := by
    intro ω
    exact finite_active_indices (fun k => τ k ω) (fun k => Δ k ω) T
      (price_exit_sequence_eventually_terminal S a T ha ω (hcad ω) (hfinite ω))
  let jumps : Ω → Finset ℕ := fun ω => (hf ω).toFinset
  have hmem : ∀ ω k, k ∈ jumps ω ↔ τ k ω < τ (k+1) ω ∧ Δ k ω ≠ 0 :=
    fun ω k => (hf ω).mem_toFinset
  refine ⟨jumps, hmem, ?_⟩
  intro k
  have hd := stopped_increment_measurable 𝓕 S hadapt hcad (τ (k+1)) (hs (k+1))
  refine ⟨hs (k+1), hd.1, ?_⟩
  have hm := active_jump_event_measurable 𝓕 (τ k) (τ (k+1)) (hs k) (hs (k+1))
    (fun ω => hmon ω k) (Δ k) hd.1
  simpa only [hmem] using hm

#print axioms active_jump_event_measurable
#print axioms finite_active_indices
#print axioms exists_measurable_active_jumps
end FTDAP
