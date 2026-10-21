import LocalMartingaleVersions
import NoArbitrageEquivalences

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- The manuscript's almost-sure price assumptions and bounded localizers. -/
structure SourcePriceHypotheses (P : Measure Ω) (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (T : NNReal) where
  adapted : ∀ t, Measurable[𝓕 t] (S t)
  initial : V
  states : Set V
  locally_finite : ∀ B : Set V, Bornology.IsBounded B → (states ∩ B).Finite
  paths : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧ S 0 ω = initial ∧
    ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ states
  localizers : ℕ → Ω → NNReal
  stopping : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
    (fun ω => (localizers n ω : WithTop NNReal))
  increasing : ∀ ω, Monotone (fun n => localizers n ω)
  eventually_horizon : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, localizers n ω = T
  bound : ℕ → ℝ
  bound_nonneg : ∀ n, 0 ≤ bound n
  bounded_stops : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
    ‖S ((min t (localizers n ω) : NNReal) : ℝ) ω‖ ≤ bound n


/-- Regularize only the exceptional paths; preserve the source localization
hypotheses and the price at every trading time outside one null set. -/
theorem exists_regular_price_hypotheses
    {P : Measure Ω} (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V) (T : NNReal)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (h : SourcePriceHypotheses P 𝓕 S T) :
    ∃ R : ℝ → Ω → V, ∃ _hR : DiscretePriceHypotheses P 𝓕 R T,
      ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), R t ω = S t ω := by
  obtain ⟨R, hRa, hRc, _hRf, _hRi, he⟩ := regular_price_version P 𝓕 hcomplete S h.adapted
    T h.initial h.states h.locally_finite h.paths
  refine ⟨R, {
    adapted := hRa
    cadlag := hRc
    states := h.states
    locally_finite := h.locally_finite
    state_paths := ?_
    localizers := h.localizers
    stopping := h.stopping
    increasing := h.increasing
    eventually_horizon := h.eventually_horizon
    bound := h.bound
    bound_nonneg := h.bound_nonneg
    bounded_stops := ?_ }, he⟩
  · filter_upwards [h.paths, he] with ω hω heω
    intro t ht
    rw [heω t ht]
    exact hω.2.2 t ht
  · intro n
    filter_upwards [h.bounded_stops n, he] with ω hω heω
    intro t ht
    have heq := heω ((min t (h.localizers n ω) : NNReal) : ℝ)
      ⟨(min t (h.localizers n ω)).property, (min_le_left _ _).trans ht⟩
    exact (congrArg norm heq).le.trans (hω t ht)

#print axioms exists_regular_price_hypotheses
end FTDAP
