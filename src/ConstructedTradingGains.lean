import NonnegativeJumpData
import GainAdapted

open MeasureTheory Set Filter Function
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The price-derived jump model gives adapted gains and predictable pre-jump
wealth for every predictable portfolio, together with the price representation. -/
theorem constructed_trading_gains
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (hfinite : ∀ ω, (Set.range (fun t => S t ω)).Finite) (T : NNReal) :
    let τ := priceExitSequence S 0 (T : ℝ)
    let ν := fun k ω => Real.toNNReal (τ (k+1) ω)
    let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
    let 𝓖 := nonnegativeFiltration 𝓕
    ∃ jumps : Ω → Finset ℕ,
      (∀ (H : NNReal × Ω → V), Measurable[𝓖.predictable] H →
        (∀ t, Measurable[𝓖 t] (finiteJumpGain jumps ν Δ H t)) ∧
        ∀ a : ℝ, Measurable[𝓖.predictable]
          (fun p : NNReal × Ω => a + preJumpGain jumps ν Δ H p.1 p.2)) ∧
      (∀ ω, Set.InjOn (fun k => ν k ω) (jumps ω : Set ℕ)) ∧
      (∀ ω k, k ∈ jumps ω → 0 < ν k ω ∧ ν k ω ≤ T ∧ Δ k ω ≠ 0) ∧
      ∀ (ω : Ω) (t : NNReal), t ≤ T → S (t : ℝ) ω - S 0 ω =
        ∑ k ∈ jumps ω, if ν k ω ≤ t then Δ k ω else 0 := by
  classical
  let τ := priceExitSequence S 0 (T : ℝ)
  let ν := fun k ω => Real.toNNReal (τ (k+1) ω)
  let Δ := fun k ω => S (τ (k+1) ω) ω - leftLim (fun t => S t ω) (τ (k+1) ω)
  obtain ⟨jumps, hdata, hinj, hbound, hrep⟩ :=
    constructed_nonnegative_jump_data 𝓕 S hadapt hcad hfinite T
  let hs := fun k => (hdata k).choose
  have hd : ∀ k, Measurable[(hs k).measurableSpace] (Δ k) :=
    fun k => (hdata k).choose_spec.1
  have hj : ∀ k, MeasurableSet[(hs k).measurableSpace] {ω | k ∈ jumps ω} :=
    fun k => (hdata k).choose_spec.2
  refine ⟨jumps, ?_, hinj, hbound, hrep⟩
  intro H hH
  exact ⟨finite_gain_adapted (nonnegativeFiltration 𝓕) jumps ν hs Δ hd hj H hH,
    pre_jump_wealth_predictable (nonnegativeFiltration 𝓕) jumps ν hs Δ hd hj H hH⟩

/-- On the compact horizon, locally finite states supply the finite-range
hypothesis used above after clamping prices outside the horizon. -/
theorem locally_finite_trading_gains
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω)) (T : NNReal)
    (s₀ : V) (hinit : ∀ ω, S 0 ω = s₀)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hstates : ∀ ω t, t ∈ Icc 0 (T : ℝ) → S t ω ∈ E) :
    let C := fun t ω => S (min (max t 0) (T : ℝ)) ω
    let τ := priceExitSequence C 0 (T : ℝ)
    let ν := fun k ω => Real.toNNReal (τ (k+1) ω)
    let Δ := fun k ω => C (τ (k+1) ω) ω - leftLim (fun t => C t ω) (τ (k+1) ω)
    let 𝓖 := nonnegativeFiltration 𝓕
    ∃ jumps : Ω → Finset ℕ,
      (∀ (H : NNReal × Ω → V), Measurable[𝓖.predictable] H →
        (∀ t, Measurable[𝓖 t] (finiteJumpGain jumps ν Δ H t)) ∧
        ∀ a : ℝ, Measurable[𝓖.predictable]
          (fun p : NNReal × Ω => a + preJumpGain jumps ν Δ H p.1 p.2)) ∧
      (∀ ω, Set.InjOn (fun k => ν k ω) (jumps ω : Set ℕ)) ∧
      (∀ ω k, k ∈ jumps ω → 0 < ν k ω ∧ ν k ω ≤ T ∧ Δ k ω ≠ 0) ∧
      ∀ (ω : Ω) (t : NNReal), t ≤ T → S (t : ℝ) ω - S 0 ω =
        ∑ k ∈ jumps ω, if ν k ω ≤ t then Δ k ω else 0 := by
  let C := fun t ω => S (min (max t 0) (T : ℝ)) ω
  have hC : ∀ ω, IsCadlag (fun t => C t ω) := fun ω =>
    cadlag_max_time (fun t => S (min t (T : ℝ)) ω)
      (cadlag_min_time _ (hcad ω) (T : ℝ)) 0
  have hfinite : ∀ ω, (Set.range (fun t => C t ω)).Finite := fun ω =>
    locally_finite_clamped_range (fun t => S t ω) (hcad ω) 0 (T : ℝ) T.2 E hE (hstates ω)
  obtain ⟨jumps, hg, hi, hb, hr⟩ := constructed_trading_gains 𝓕 C
    (clamped_price_adapted 𝓕 S hadapt 0 (T : ℝ) T.2 s₀ hinit) hC hfinite T
  refine ⟨jumps, hg, hi, hb, ?_⟩
  intro ω t ht
  have h := hr ω t ht
  have hc : C (t : ℝ) ω = S (t : ℝ) ω := by
    dsimp only [C]
    rw [max_eq_left (show (0 : ℝ) ≤ (t : ℝ) from t.2), min_eq_left (show (t : ℝ) ≤ (T : ℝ) from ht)]
  have hz : C 0 ω = S 0 ω := by
    dsimp only [C]
    rw [max_self, min_eq_left (show (0 : ℝ) ≤ (T : ℝ) from T.2)]
  rw [hc, hz] at h
  exact h

#print axioms locally_finite_trading_gains
#print axioms constructed_trading_gains
end FTDAP
