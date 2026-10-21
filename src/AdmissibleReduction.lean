import GainAdapted
import LocalPortfolioReduction

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace FTDAP
variable {Ω ι V : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [DenselyOrdered ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The common predictable reduction uses the actual pre-jump wealth of each
admissible strategy. Wealth measurability and face compatibility are derived. -/
theorem admissible_local_portfolio_reduction (P : Measure Ω)
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι)
    (hτ : ∀ k, IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ι)))
    (Δ : ℕ → Ω → V)
    (hΔ : ∀ k, Measurable[(hτ k).measurableSpace] (Δ k))
    (hactive : ∀ k, MeasurableSet[(hτ k).measurableSpace] {ω | k ∈ jumps ω})
    (T : ι) (F : ℕ → Finset V) (index : ι × Ω → ℕ)
    (hindex : Measurable[𝓕.predictable] index)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (horizon : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, ⊥ < τ k ω ∧ τ k ω ≤ T)
    (hinj : ∀ᵐ ω ∂P, Set.InjOn (fun k => τ k ω) (jumps ω))
    (hincrements : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ F (index (τ k ω, ω))) :
    ∃ c : ι × Ω → ℝ, Measurable[𝓕.predictable] c ∧ (∀ p, 1 ≤ c p) ∧
      ∀ (H : ι × Ω → V) (a : ℝ), Measurable[𝓕.predictable] H →
      (∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain jumps τ Δ H t ω) →
      ∃ G : ι × Ω → V, Measurable[𝓕.predictable] G ∧
        (∀ᵐ ω ∂P, ∀ t, finiteJumpGain jumps τ Δ G t ω = finiteJumpGain jumps τ Δ H t ω) ∧
        ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, ‖G (τ k ω, ω)‖ ≤
          c (τ k ω, ω) * (a + preJumpGain jumps τ Δ H (τ k ω) ω) := by
  obtain ⟨c, hcm, hc, hreduce⟩ := local_market_portfolio_reduction P 𝓕 jumps τ Δ T F index
    hindex hna (horizon.mono (fun ω h k hk => (h k hk).2)) hincrements
  refine ⟨c, hcm, hc, ?_⟩
  intro H a hH hadm
  let W : ι × Ω → ℝ := fun p => a + preJumpGain jumps τ Δ H p.1 p.2
  have hW : Measurable[𝓕.predictable] W :=
    pre_jump_wealth_predictable 𝓕 jumps τ hτ Δ hΔ hactive H hH a
  have hnonneg : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, 0 ≤ W (τ k ω, ω) := by
    filter_upwards [hadm, horizon] with ω hb hh k hk
    have : NeBot (𝓝[<] (τ k ω)) := nhdsLT_neBot_of_exists_lt ⟨⊥, (hh k hk).1⟩
    have hp := pre_jump_gain_lower_bound jumps τ Δ H (τ k ω) T ω a (hh k hk).2 hb
    change 0 ≤ a + preJumpGain jumps τ Δ H (τ k ω) ω
    linarith
  have hconstraint : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω,
      -W (τ k ω, ω) ≤ ⟪H (τ k ω, ω), Δ k ω⟫ := by
    filter_upwards [hadm, horizon, hinj] with ω hb hh hi k hk
    exact jump_wealth_compatibility jumps τ Δ H ω k hk hi a (hb _ (hh k hk).2)
  exact hreduce H W hH hW hnonneg hconstraint

#print axioms admissible_local_portfolio_reduction
end FTDAP
