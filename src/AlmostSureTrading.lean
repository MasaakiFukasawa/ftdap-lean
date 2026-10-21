import NullPathRepair

open MeasureTheory Set Filter Function
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Finite jump data for the original prices, with all stopping-time information
needed to define predictable trading gains. -/
structure PriceJumpModel (P : Measure Ω) (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (S : NNReal → Ω → V) (T : NNReal) where
  active : Ω → Finset ℕ
  times : ℕ → Ω → NNReal
  marks : ℕ → Ω → V
  stopping : ∀ k, IsStoppingTime 𝓕 (fun ω => WithTop.some (times k ω))
  measurable_marks : ∀ k, Measurable[(stopping k).measurableSpace] (marks k)
  measurable_active : ∀ k, MeasurableSet[(stopping k).measurableSpace] {ω | k ∈ active ω}
  injective_times : ∀ ω, Set.InjOn (fun k => times k ω) (active ω : Set ℕ)
  bounds : ∀ ω k, k ∈ active ω → 0 < times k ω ∧ times k ω ≤ T ∧ marks k ω ≠ 0
  representation : ∀ᵐ ω ∂P, ∀ t ≤ T, S t ω - S 0 ω =
    ∑ k ∈ active ω, if times k ω ≤ t then marks k ω else 0

omit [InnerProductSpace ℝ V] in
/-- The almost-sure price assumptions construct a jump model; no measurable
jump enumeration or gain adaptedness is assumed as input. -/
theorem exists_price_jump_model
    (P : Measure Ω) (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (T : NNReal) (s₀ : V)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧ S 0 ω = s₀ ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E) :
    Nonempty (PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T) := by
  classical
  obtain ⟨R, hRa, hRc, hRf, _hRi, hsame⟩ :=
    regular_price_version P 𝓕 hcomplete S hadapt T s₀ E hE hpath
  let τ := priceExitSequence R 0 (T : ℝ)
  let ν := fun k ω => Real.toNNReal (τ (k+1) ω)
  let Δ := fun k ω => R (τ (k+1) ω) ω - leftLim (fun t => R t ω) (τ (k+1) ω)
  obtain ⟨jumps, hdata, hi, hb, hr⟩ :=
    constructed_nonnegative_jump_data 𝓕 R hRa hRc hRf T
  let hs := fun k => (hdata k).choose
  refine ⟨{
    active := jumps
    times := ν
    marks := Δ
    stopping := hs
    measurable_marks := fun k => (hdata k).choose_spec.1
    measurable_active := fun k => (hdata k).choose_spec.2
    injective_times := hi
    bounds := hb
    representation := ?_ }⟩
  filter_upwards [hsame] with ω hω
  intro t ht
  have h := hr ω t ht
  have ht' : (t : ℝ) ∈ Icc 0 (T : ℝ) := ⟨t.2, ht⟩
  have hz : (0 : ℝ) ∈ Icc 0 (T : ℝ) := ⟨le_rfl, T.2⟩
  rw [hω (t : ℝ) ht', hω 0 hz] at h
  exact h

/-- Gains in the price-derived model are adapted for every predictable holding. -/
theorem PriceJumpModel.gain_adapted
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H) (t : NNReal) :
    Measurable[𝓕 t] (finiteJumpGain M.active M.times M.marks H t) := by
  exact finite_gain_adapted 𝓕 M.active M.times M.stopping M.marks
    M.measurable_marks M.measurable_active H hH t

/-- Pre-jump wealth in the same model is predictable. -/
theorem PriceJumpModel.pre_wealth_predictable
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H) (a : ℝ) :
    Measurable[𝓕.predictable]
      (fun p : NNReal × Ω => a + preJumpGain M.active M.times M.marks H p.1 p.2) := by
  exact pre_jump_wealth_predictable 𝓕 M.active M.times M.stopping M.marks
    M.measurable_marks M.measurable_active H hH a

#print axioms exists_price_jump_model
#print axioms PriceJumpModel.gain_adapted
#print axioms PriceJumpModel.pre_wealth_predictable
end FTDAP
