import ModelJumpIdentification
import AdmissibleReduction

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The original price assumptions and NA supply the common predictable
portfolio reduction. Finite increment sets, their predictable region index,
and compatibility with the actual jump marks are all derived. -/
theorem PriceJumpModel.portfolio_reduction_from_prices
    {P : Measure Ω} (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (T : NNReal)
    (M : PriceJumpModel P 𝓕 (fun t => S (t : ℝ)) T)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ m, IsStoppingTime 𝓕 (fun ω => (σ m ω : WithTop NNReal)))
    (hcover : ∀ᵐ ω ∂P, ∃ m, T ≤ σ m ω)
    (b : ℕ → ℝ)
    (hbound : ∀ m, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ m ω) : NNReal) : ℝ) ω‖ ≤ b m)
    (hna : GainNoArbitrage P 𝓕 M.active M.times M.marks T) :
    ∃ c : NNReal × Ω → ℝ, Measurable[𝓕.predictable] c ∧ (∀ p, 1 ≤ c p) ∧
      ∀ (H : NNReal × Ω → V) (a : ℝ), Measurable[𝓕.predictable] H →
      (∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks H t ω) →
      ∃ G : NNReal × Ω → V, Measurable[𝓕.predictable] G ∧
        (∀ᵐ ω ∂P, ∀ t, finiteJumpGain M.active M.times M.marks G t ω =
          finiteJumpGain M.active M.times M.marks H t ω) ∧
        ∀ᵐ ω ∂P, ∀ k ∈ M.active ω, ‖G (M.times k ω, ω)‖ ≤
          c (M.times k ω, ω) * (a + preJumpGain M.active M.times M.marks H (M.times k ω) ω) := by
  obtain ⟨index, F, him, hF⟩ := predictable_stopped_increment_sets P 𝓕 S T E hE hpath
    σ hσ hcover b hbound
  have hmarks := M.marks_eq_price_jumps S T (hpath.mono (fun _ h => h.1))
  have hincrements : ∀ᵐ ω ∂P, ∀ k ∈ M.active ω,
      M.marks k ω ∈ F (index (M.times k ω, ω)) := by
    filter_upwards [hF, hmarks] with ω hω hm
    intro k hk
    rw [hm k hk]
    exact hω _ (M.bounds ω k hk).1 (M.bounds ω k hk).2.1
  exact admissible_local_portfolio_reduction P 𝓕 M.active M.times M.stopping M.marks
    M.measurable_marks M.measurable_active T F index him hna
    (Eventually.of_forall (fun ω k hk => ⟨(M.bounds ω k hk).1, (M.bounds ω k hk).2.1⟩))
    (Eventually.of_forall M.injective_times) hincrements

#print axioms PriceJumpModel.portfolio_reduction_from_prices
end FTDAP
