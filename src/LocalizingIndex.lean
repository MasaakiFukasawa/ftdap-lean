import LocalPortfolioReduction

open MeasureTheory Set
namespace FTDAP
variable {Ω ι : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [OrderClosedTopology ι]
    [SecondCountableTopology ι] [OrderTopology ι] [DenselyOrdered ι]

/-- The localizing region index is predictable, including a measurable
default region where no stopping time covers the point. -/
theorem predictable_localizing_index (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (σ : ℕ → Ω → ι)
    (hσ : ∀ m, IsStoppingTime 𝓕 (fun ω => (σ m ω : WithTop ι))) :
    ∃ index : ι × Ω → ℕ, Measurable[𝓕.predictable] index ∧
      ∀ p, (∃ m, p.1 ≤ σ m p.2) →
        ∃ m, index p = m + 1 ∧ p.1 ≤ σ m p.2 := by
  classical
  let pred : (ι × Ω) → ℕ → Prop := fun p n =>
    if n = 0 then ¬ ∃ m, p.1 ≤ σ m p.2 else p.1 ≤ σ (n - 1) p.2
  have hex : ∀ p, ∃ n, pred p n := by
    intro p
    by_cases h : ∃ m, p.1 ≤ σ m p.2
    · obtain ⟨m, hm⟩ := h
      exact ⟨m + 1, by simpa [pred] using hm⟩
    · exact ⟨0, by simpa [pred] using h⟩
  have hpmeas : ∀ n, MeasurableSet[𝓕.predictable] {p | pred p n} := by
    intro n
    cases n with
    | zero =>
      have hcover : MeasurableSet[𝓕.predictable] (⋃ m, {p : ι × Ω | p.1 ≤ σ m p.2}) :=
        MeasurableSet.iUnion (fun m => predictable_stopped_interval 𝓕 (σ m) (hσ m))
      convert hcover.compl using 1
      ext p
      simp [pred]
    | succ m =>
      simpa [pred] using predictable_stopped_interval 𝓕 (σ m) (hσ m)
  let index : ι × Ω → ℕ := fun p => Nat.find (hex p)
  refine ⟨index, measurable_find hex hpmeas, ?_⟩
  intro p hcovered
  have hspec : pred p (index p) := Nat.find_spec (hex p)
  have hnonzero : index p ≠ 0 := by
    intro hz
    have hn : ¬ ∃ m, p.1 ≤ σ m p.2 := by simpa [hz, pred] using hspec
    exact hn hcovered
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
  refine ⟨m, hm, ?_⟩
  simpa [hm, pred] using hspec

#print axioms predictable_localizing_index
end FTDAP
