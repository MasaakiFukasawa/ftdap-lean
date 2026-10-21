import PriceLpRepresentatives
import ClaimSliceConvex

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A common unit Hilbert reduction, with the actual gain-preservation property. -/
def HasUnitHilbertReduction
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) : Prop :=
  ∀ (H : NNReal × Ω → V), Measurable[𝓕.predictable] H →
    (∀ᵐ ω ∂P, ∀ t ≤ T, -1 ≤ finiteJumpGain M.active M.times M.marks H t ω) →
    ∃ G : NNReal × Ω → V, Measurable[𝓕.predictable] G ∧
      (∀ᵐ ω ∂P, ∀ t, finiteJumpGain M.active M.times M.marks G t ω =
        finiteJumpGain M.active M.times M.marks H t ω) ∧
      ∃ hL : MemLp G 2 (M.energyMeasure c), ‖hL.toLp G‖ ≤ 1

variable [CompleteSpace V]

/-- The source-derived Hilbert reduction instantiates the actual weak-star
closedness theorem for every fixed lower-bound, bounded-payoff slice. -/
theorem PriceJumpModel.hilbert_slice_weakstar_closed
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (hreduction : HasUnitHilbertReduction M c) (a r : ℝ) (ha : 0 < a) :
    let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
    IsClosed {f : WeakClaims P | claimInL2 P (claimValue P f) ∈
      lpClaimSlice P M.active M.times (fun k ω => (M.times k ω, ω)) M.marks
        (M.energyWeight c) a r T} := by
  have hatom : ∀ k, @Measurable Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable
      (fun ω => (M.times k ω, ω)) := fun k =>
    measurable_predictable_atom 𝓕 (M.times k) (M.stopping k).measurable'.untopA
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  apply claim_slice_weakstar_closed P M.active M.times (fun k ω => (M.times k ω, ω))
    M.marks (M.energyWeight c) hatom (M.energyWeight_measurable c hcm)
    (Eventually.of_forall (fun ω k hk => ne_of_gt (M.energyWeight_positive c hc ω k hk)))
    a r a T
  intro f hf
  obtain ⟨_hfb, H, hHa, hHf⟩ := hf
  have hH : Measurable[𝓕.predictable] (H : NNReal × Ω → V) := H.val.stronglyMeasurable.measurable
  have hadm : ∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks H t ω := by
    filter_upwards [hHa] with ω hω
    intro t _
    exact hω t
  obtain ⟨Y, hYnorm, hYe⟩ := M.lp_representative_from_unit_reduction c hcm hc hreduction H hH a ha hadm
  refine ⟨Y, hYnorm, ?_, ?_⟩
  · filter_upwards [hHa, hYe] with ω hω he
    intro t
    change -a ≤ finiteJumpGain M.active M.times M.marks Y t ω
    rw [he t]
    exact hω t
  · filter_upwards [hHf, hYe] with ω hω he
    change f ω ≤ finiteJumpGain M.active M.times M.marks Y T ω
    rw [he T]
    exact hω

omit [CompleteSpace V] in
/-- On a bounded payoff slice, the actual admissible trading cone equals the
explicit Hilbert claim slice. The uniform all-time lower bound is derived by
the NA continuation argument, not imposed on the original cone witness. -/
theorem PriceJumpModel.bounded_claim_slice_iff
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (hreduction : HasUnitHilbertReduction M c)
    (hna : GainNoArbitrage P 𝓕 M.active M.times M.marks T)
    (a r : ℝ) (ha : 0 < a) (hra : r ≤ a)
    (f : Lp ℝ ∞ P) (hfb : ∀ᵐ ω ∂P, |f ω| ≤ r) :
    let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
    claimInL2 P f ∈ lpClaimSlice P M.active M.times (fun k ω => (M.times k ω, ω))
        M.marks (M.energyWeight c) a r T ↔
      weakClaim P f ∈ tradingCone P 𝓕 M.active M.times M.marks T := by
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  have hf : claimInL2 P f =ᵐ[P] f := ((Lp.memLp f).mono_exponent (p := 2) le_top).coeFn_toLp
  constructor
  · rintro ⟨_hb, H, hHa, hHf⟩
    refine ⟨H, ⟨H.val.stronglyMeasurable.measurable, a, ha, ?_⟩, ?_⟩
    · filter_upwards [hHa] with ω hω
      intro t _
      exact hω t
    · filter_upwards [hHf, hf] with ω hω hfω
      change f ω ≤ finiteJumpGain M.active M.times M.marks H T ω
      rwa [hfω] at hω
  · rintro ⟨H, ⟨hH, b, hb, hHb⟩, hdom⟩
    have hterminal : ∀ᵐ ω ∂P, -a ≤ finiteJumpGain M.active M.times M.marks H T ω := by
      filter_upwards [hfb, hdom] with ω hω hd
      have hl := (abs_le.mp hω).1
      change f ω ≤ finiteJumpGain M.active M.times M.marks H T ω at hd
      linarith
    have hA := continuation_all_times P 𝓕 M.active M.times M.marks T hna H hH a b ha hb
      hHb hterminal (M.gain_adapted H hH)
    obtain ⟨Y, _hYnorm, hYe⟩ := M.lp_representative_from_unit_reduction c hcm hc hreduction H hH a ha hA
    refine ⟨?_, Y, ?_, ?_⟩
    · filter_upwards [hfb, hf] with ω hω hfω
      rw [hfω]
      exact hω
    · filter_upwards [hA, hYe] with ω hω he
      intro t
      change -a ≤ finiteJumpGain M.active M.times M.marks Y t ω
      rw [he t, M.gain_clamped_horizon H t ω]
      exact hω _ (min_le_right _ _)
    · filter_upwards [hdom, hf, hYe] with ω hd hfω he
      change claimInL2 P f ω ≤ finiteJumpGain M.active M.times M.marks Y T ω
      rw [hfω, he T]
      exact hd

/-- Every bounded slice of the actual admissible trading cone is weak-star
closed. Its identification with the Hilbert slice is proved above. -/
theorem PriceJumpModel.bounded_trading_slice_closed
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (hreduction : HasUnitHilbertReduction M c)
    (hna : GainNoArbitrage P 𝓕 M.active M.times M.marks T) (r : ℝ) :
    IsClosed {f : WeakClaims P | f ∈ tradingCone P 𝓕 M.active M.times M.marks T ∧
      ∀ᵐ ω ∂P, |claimValue P f ω| ≤ r} := by
  let a := max r 0 + 1
  have ha : 0 < a := by dsimp only [a]; linarith [le_max_right r 0]
  have hra : r ≤ a := by dsimp only [a]; linarith [le_max_left r 0]
  have hclosed := M.hilbert_slice_weakstar_closed c hcm hc hreduction a r ha
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  have heq : {f : WeakClaims P | f ∈ tradingCone P 𝓕 M.active M.times M.marks T ∧
      ∀ᵐ ω ∂P, |claimValue P f ω| ≤ r} =
      {f : WeakClaims P | claimInL2 P (claimValue P f) ∈
        lpClaimSlice P M.active M.times (fun k ω => (M.times k ω, ω)) M.marks
          (M.energyWeight c) a r T} := by
    ext f
    constructor
    · rintro ⟨hf, hb⟩
      exact (M.bounded_claim_slice_iff c hcm hc hreduction hna a r ha hra (claimValue P f) hb).mpr hf
    · intro hf
      have hcoe : claimInL2 P (claimValue P f) =ᵐ[P] claimValue P f :=
        ((Lp.memLp (claimValue P f)).mono_exponent (p := 2) le_top).coeFn_toLp
      have hb : ∀ᵐ ω ∂P, |claimValue P f ω| ≤ r := by
        filter_upwards [hf.1, hcoe] with ω hω he
        rwa [he] at hω
      exact ⟨(M.bounded_claim_slice_iff c hcm hc hreduction hna a r ha hra (claimValue P f) hb).mp hf, hb⟩
  rw [heq]
  exact hclosed

#print axioms PriceJumpModel.bounded_trading_slice_closed
#print axioms PriceJumpModel.bounded_claim_slice_iff
#print axioms PriceJumpModel.hilbert_slice_weakstar_closed
end FTDAP
