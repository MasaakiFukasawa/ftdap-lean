import SourceEnvelopeBound

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [MeasurableSpace Ω] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Equality of entire gains also preserves pre-jump gain at each positive time. -/
theorem pre_gain_eq_of_gain_eq
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → NNReal) (Δ : ℕ → Ω → V)
    (G H : NNReal × Ω → V) (ω : Ω)
    (he : ∀ t, finiteJumpGain jumps τ Δ G t ω = finiteJumpGain jumps τ Δ H t ω)
    (t : NNReal) (ht : 0 < t) :
    preJumpGain jumps τ Δ G t ω = preJumpGain jumps τ Δ H t ω := by
  have : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  apply tendsto_nhds_unique (finite_gain_left_limit jumps τ Δ G t ω)
  exact (finite_gain_left_limit jumps τ Δ H t ω).congr'
    (Eventually.of_forall (fun s => (he s).symm))

variable [FiniteDimensional ℝ V]

/-- NA and the source price assumptions construct one predictable finite
measure for which all unit-admissible gains have gain-preserving unit-L2
portfolio representatives. Neither a common measure nor a uniform Hilbert
bound is assumed. -/
theorem PriceJumpModel.unit_hilbert_reduction_from_prices
    {P : Measure Ω} [IsProbabilityMeasure P] (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
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
      M.energyMeasure c univ ≤ 1 ∧
      ∀ (H : NNReal × Ω → V), Measurable[𝓕.predictable] H →
      (∀ᵐ ω ∂P, ∀ t ≤ T, -1 ≤ finiteJumpGain M.active M.times M.marks H t ω) →
      ∃ G : NNReal × Ω → V, Measurable[𝓕.predictable] G ∧
        (∀ᵐ ω ∂P, ∀ t, finiteJumpGain M.active M.times M.marks G t ω =
          finiteJumpGain M.active M.times M.marks H t ω) ∧
        ∃ hL : MemLp G 2 (M.energyMeasure c), ‖hL.toLp G‖ ≤ 1 := by
  obtain ⟨c, hcm, hc, hreduce⟩ := M.portfolio_reduction_from_prices 𝓕 S T E hE hpath
    σ hσ hcover b hbound hna
  refine ⟨c, hcm, hc, M.energyMeasure_mass c hcm hc, ?_⟩
  intro H hH hadm
  obtain ⟨G, hG, he, hn⟩ := hreduce H 1 hH hadm
  refine ⟨G, hG, he, M.energy_of_pre_wealth_bound c hcm hc G hG ?_⟩
  filter_upwards [he, hn] with ω hω hnorm
  intro k hk
  have hp := pre_gain_eq_of_gain_eq M.active M.times M.marks G H ω hω
    (M.times k ω) (M.bounds ω k hk).1
  rw [hp]
  exact hnorm k hk

#print axioms pre_gain_eq_of_gain_eq
#print axioms PriceJumpModel.unit_hilbert_reduction_from_prices
end FTDAP
