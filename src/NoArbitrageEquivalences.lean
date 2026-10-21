import DiscretePriceFTAP

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The identity from the norm topology of bounded claims to σ(L∞, L1). -/
theorem weakClaim_continuous (P : Measure Ω) : Continuous (weakClaim P) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro Z
  exact ((claimsPairingCLM P).flip Z).continuous

/-- NFL and NFLVR use their respective full topological closures. -/
def ConeNFL (P : Measure Ω) (C : Set (WeakClaims P)) : Prop :=
  ∀ f ∈ closure C, 0 ≤ claimValue P f → f = 0

def ConeNFLVR (P : Measure Ω) (C : Set (WeakClaims P)) : Prop :=
  ∀ f ∈ closure ((weakClaim P) ⁻¹' C), 0 ≤ f → f = 0

theorem cone_nfl_implies_nflvr (P : Measure Ω) (C : Set (WeakClaims P))
    (h : ConeNFL P C) : ConeNFLVR P C := by
  intro f hf hp
  exact h (weakClaim P f)
    (map_mem_closure (weakClaim_continuous P) hf (fun _ hx => hx)) hp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- All three no-arbitrage conditions coincide for locally finite prices.
The norm closure in NFLVR and weak-star closure in NFL are both actual
closures in the corresponding Lean topological spaces. -/
theorem PriceJumpModel.no_arbitrage_equivalences
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (h : DiscretePriceHypotheses P 𝓕 S T) :
    let C := tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
    (GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T ↔ ConeNFLVR P C) ∧
    (GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T ↔ ConeNFL P C) := by
  let C := tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
  have hcna := trading_cone_no_arbitrage_iff P (nonnegativeFiltration 𝓕)
    M.active M.times M.marks T (fun H hH =>
      (M.gain_adapted H hH T).mono ((nonnegativeFiltration 𝓕).le T) le_rfl)
  have hnaNFL : GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T →
      ConeNFL P C := by
    intro hna
    have hcover : ∀ᵐ ω ∂P, ∃ n, T ≤ h.localizers n ω := by
      filter_upwards [h.eventually_horizon] with ω hω
      obtain ⟨N, hN⟩ := hω
      exact ⟨N, (hN N le_rfl).ge⟩
    have hclosed := M.trading_cone_closed_from_prices (nonnegativeFiltration 𝓕) S T
      h.states h.locally_finite (h.state_paths.mono (fun ω hω => ⟨h.cadlag ω, hω⟩))
      h.localizers h.stopping hcover h.bound h.bounded_stops hna
    intro f hf hp
    exact hcna.mpr hna f (hclosed.closure_eq ▸ hf) hp
  have hnflvrNA : ConeNFLVR P C →
      GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T := by
    intro hnflvr
    apply hcna.mp
    intro f hf hp
    exact hnflvr (claimValue P f) (subset_closure hf) hp
  exact ⟨⟨fun hna => cone_nfl_implies_nflvr P C (hnaNFL hna), hnflvrNA⟩,
    ⟨hnaNFL, fun hnfl => hnflvrNA (cone_nfl_implies_nflvr P C hnfl)⟩⟩

#print axioms weakClaim_continuous
#print axioms cone_nfl_implies_nflvr
#print axioms PriceJumpModel.no_arbitrage_equivalences
end FTDAP
