import FinitePortfolioReduction

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace FTDAP
variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Countably many finite increment sets give a measurable, finite, common
bound, without a deterministic global increment set or a moment assumption. -/
theorem measurable_local_portfolio_reduction (F : ℕ → Finset V)
    (index : α → ℕ) (hindex : Measurable index) :
    ∃ c : α → ℝ, Measurable c ∧ (∀ p, 1 ≤ c p) ∧
      ∀ (H : α → V) (W : α → ℝ), Measurable H → Measurable W →
      ∃ U G : α → V, Measurable U ∧ Measurable G ∧
        (∀ p, NonnegOn (constraintSet (F (index p)) H W p) (U p)) ∧
        (∀ p, 0 ≤ W p → ‖G p‖ ≤ c p * W p) ∧
        ∀ p z, z ∈ zeroFace (constraintSet (F (index p)) H W p) (U p) →
          ⟪G p, z⟫ = ⟪H p, z⟫ := by
  classical
  choose c hc hreduce using (fun m => measurable_finite_portfolio_reduction (α := α) (F m))
  refine ⟨fun p => c (index p), (measurable_of_countable c).comp hindex,
    fun p => hc (index p), ?_⟩
  intro H W hH hW
  choose U G hU hG hsep hnorm hpreserve using (fun m => hreduce m H W hH hW)
  have hUm : Measurable (fun p => U (index p) p) :=
    (measurable_from_prod_countable_right (f := fun q : ℕ × α => U q.1 q.2) hU).comp
      (hindex.prodMk measurable_id)
  have hGm : Measurable (fun p => G (index p) p) :=
    (measurable_from_prod_countable_right (f := fun q : ℕ × α => G q.1 q.2) hG).comp
      (hindex.prodMk measurable_id)
  exact ⟨fun p => U (index p) p, fun p => G (index p) p,
    hUm, hGm, fun p => hsep (index p) p,
    fun p hp => hnorm (index p) p hp,
    fun p z hz => hpreserve (index p) p z hz⟩

end FTDAP

namespace FTDAP
variable {Ω ι V : Type*} [MeasurableSpace Ω] [LinearOrder ι] [OrderBot ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

theorem local_market_portfolio_reduction (P : Measure Ω)
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (F : ℕ → Finset V) (index : ι × Ω → ℕ) (hindex : Measurable[𝓕.predictable] index)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (horizon : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, τ k ω ≤ T)
    (hincrements : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ F (index (τ k ω, ω))) :
    ∃ c : ι × Ω → ℝ, Measurable[𝓕.predictable] c ∧ (∀ p, 1 ≤ c p) ∧
      ∀ (H : ι × Ω → V) (W : ι × Ω → ℝ),
      Measurable[𝓕.predictable] H → Measurable[𝓕.predictable] W →
      (∀ᵐ ω ∂P, ∀ k ∈ jumps ω, 0 ≤ W (τ k ω, ω)) →
      (∀ᵐ ω ∂P, ∀ k ∈ jumps ω, -W (τ k ω, ω) ≤ ⟪H (τ k ω, ω), Δ k ω⟫) →
      ∃ G : ι × Ω → V, Measurable[𝓕.predictable] G ∧
        (∀ᵐ ω ∂P, ∀ t, finiteJumpGain jumps τ Δ G t ω = finiteJumpGain jumps τ Δ H t ω) ∧
        ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, ‖G (τ k ω, ω)‖ ≤ c (τ k ω, ω) * W (τ k ω, ω) := by
  let : MeasurableSpace (ι × Ω) := 𝓕.predictable
  obtain ⟨c, hcmeas, hc, hreduce⟩ := measurable_local_portfolio_reduction F index hindex
  refine ⟨c, hcmeas, hc, ?_⟩
  intro H W hH hW hWpos hconstraint
  obtain ⟨U, G, hU, hG, hnonneg, hnorm, hpreserve⟩ := hreduce H W hH hW
  let J : ι × Ω → Finset V := fun p => constraintSet (F (index p)) H W p
  have hactual : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ J (τ k ω, ω) := by
    filter_upwards [hincrements, hconstraint] with ω hω hω' k hk
    exact Finset.mem_filter.mpr ⟨hω k hk, hω' k hk⟩
  have hz := actual_increment_zero_face P 𝓕 jumps τ Δ T hna J U hU horizon hactual hnonneg
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hz] with ω hω t
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkt : τ k ω ≤ t
    · simp only [ite_eq_left hkt]
      exact hpreserve (τ k ω, ω) (Δ k ω) (hω k hk)
    · simp [hkt]
  · filter_upwards [hWpos] with ω hω k hk
    exact hnorm (τ k ω, ω) (hω k hk)

#print axioms measurable_local_portfolio_reduction
#print axioms local_market_portfolio_reduction
end FTDAP
