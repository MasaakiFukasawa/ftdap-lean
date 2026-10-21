import ModelTransport

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- The price and localization hypotheses, independent of any arbitrage
condition or martingale measure. -/
structure DiscretePriceHypotheses (P : Measure Ω) (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (T : NNReal) where
  adapted : ∀ t, Measurable[𝓕 t] (S t)
  cadlag : ∀ ω, IsCadlag (fun t => S t ω)
  states : Set V
  locally_finite : ∀ B : Set V, Bornology.IsBounded B → (states ∩ B).Finite
  state_paths : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ states
  localizers : ℕ → Ω → NNReal
  stopping : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
    (fun ω => (localizers n ω : WithTop NNReal))
  increasing : ∀ ω, Monotone (fun n => localizers n ω)
  eventually_horizon : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, localizers n ω = T
  bound : ℕ → ℝ
  bound_nonneg : ∀ n, 0 ≤ bound n
  bounded_stops : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
    ‖S ((min t (localizers n ω) : NNReal) : ℝ) ω‖ ≤ bound n

variable [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [BorelSpace V] [SecondCountableTopology V]

/-- NA and the existence of an equivalent local martingale probability are
equivalent for the actual finite-jump model of locally finite prices. -/
theorem PriceJumpModel.discrete_price_ftap
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (h : DiscretePriceHypotheses P 𝓕 S T) :
    GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T ↔
      ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
        HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T := by
  constructor
  · intro hna
    exact M.na_implies_equivalent_local_martingale_measure 𝓕 S h.adapted h.cadlag T hna
      h.states h.locally_finite h.state_paths h.localizers h.stopping h.increasing
      h.eventually_horizon h.bound h.bound_nonneg h.bounded_stops
  · rintro ⟨Q, hQ, hQP, hPQ, hlm⟩
    let := hQ
    have hna := (M.change_measure hQP).local_martingale_implies_na 𝓕 S h.adapted h.cadlag T
      h.states h.locally_finite (hQP.ae_le h.state_paths) h.localizers h.stopping
      (hQP.ae_le h.eventually_horizon) h.bound h.bound_nonneg
      (fun n => hQP.ae_le (h.bounded_stops n)) hlm
    exact gain_na_of_equivalent_measure hQP hPQ (nonnegativeFiltration 𝓕)
      M.active M.times M.marks T hna

#print axioms PriceJumpModel.discrete_price_ftap
end FTDAP
