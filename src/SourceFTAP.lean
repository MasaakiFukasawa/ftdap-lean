import AlmostSurePriceHypotheses

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Full FTAP equivalences for the source price with almost-sure path
assumptions. Exceptional-path regularization is transported back to the
original process under every equivalent martingale measure. -/
theorem PriceJumpModel.source_price_ftap
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V) (T : NNReal)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (h : SourcePriceHypotheses P 𝓕 S T)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T) :
    let NA := GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
    let C := tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
    (NA ↔ ConeNFLVR P C) ∧ (NA ↔ ConeNFL P C) ∧
      (NA ↔ ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
        HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T) ∧
      (NA → IsClosed C) := by
  obtain ⟨R, hR, he⟩ := exists_regular_price_hypotheses 𝓕 S T hcomplete h
  have heN : ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T → R (t : ℝ) ω = S (t : ℝ) ω := by
    filter_upwards [he] with ω hω
    intro t ht
    exact hω _ ⟨t.property, ht⟩
  let MR := M.congr_prices heN
  have hequiv := MR.no_arbitrage_equivalences 𝓕 R T hR
  refine ⟨hequiv.1, hequiv.2, ⟨?_, ?_⟩, ?_⟩
  · intro hna
    obtain ⟨Q, hQ, hQP, hPQ, hlmR⟩ := (MR.discrete_price_ftap 𝓕 R T hR).mp hna
    refine ⟨Q, hQ, hQP, hPQ, ?_⟩
    apply horizon_local_martingale_congr hlmR (hQP.ae_le heN)
    intro σ hσ
    apply horizon_stopped_adapted_of_regular_version 𝓕
      (fun N hN => hcomplete N (hPQ hN)) R S T hR.adapted hR.cadlag
      (hQP.ae_le (he.mono (fun _ hω t ht => (hω t ht).symm))) σ hσ
  · rintro ⟨Q, hQ, hQP, hPQ, hlmS⟩
    have heSN : ∀ᵐ ω ∂Q, ∀ t : NNReal, t ≤ T → S (t : ℝ) ω = R (t : ℝ) ω :=
      hQP.ae_le (heN.mono (fun _ hω t ht => (hω t ht).symm))
    have hlmR := horizon_local_martingale_congr hlmS heSN (fun σ hσ t =>
      stopped_price_strongly_adapted 𝓕 R hR.adapted hR.cadlag σ hσ t.val)
    exact (MR.discrete_price_ftap 𝓕 R T hR).mpr ⟨Q, hQ, hQP, hPQ, hlmR⟩
  · intro hna
    have hcover : ∀ᵐ ω ∂P, ∃ n, T ≤ h.localizers n ω := by
      filter_upwards [h.eventually_horizon] with ω hω
      obtain ⟨N, hN⟩ := hω
      exact ⟨N, (hN N le_rfl).ge⟩
    exact M.trading_cone_closed_from_prices (nonnegativeFiltration 𝓕) S T h.states
      h.locally_finite (h.paths.mono (fun _ hω => ⟨hω.1, hω.2.2⟩))
      h.localizers h.stopping hcover h.bound h.bounded_stops hna

/-- The source assumptions themselves supply the jump model used by the full
FTAP, so no enumeration or gain-measurability hypothesis is needed. -/
theorem source_price_ftap_with_constructed_model
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → V) (T : NNReal)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (h : SourcePriceHypotheses P 𝓕 S T) :
    ∃ M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T,
      let NA := GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
      let C := tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
      (NA ↔ ConeNFLVR P C) ∧ (NA ↔ ConeNFL P C) ∧
        (NA ↔ ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
          HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T) ∧
        (NA → IsClosed C) := by
  obtain ⟨M⟩ := exists_price_jump_model P 𝓕 hcomplete S h.adapted T h.initial
    h.states h.locally_finite h.paths
  exact ⟨M, M.source_price_ftap 𝓕 S T hcomplete h⟩

#print axioms PriceJumpModel.source_price_ftap
#print axioms source_price_ftap_with_constructed_model
end FTDAP
