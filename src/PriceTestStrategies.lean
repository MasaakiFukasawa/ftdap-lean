import StoppedTradingGains

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- Constant portfolios test the price itself in the constructed jump model. -/
theorem PriceJumpModel.constant_gain_representation
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T) (v : V) :
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      finiteJumpGain M.active M.times M.marks (fun _ => v) t ω =
        inner ℝ v (S t ω - S 0 ω) := by
  classical
  filter_upwards [M.representation] with ω hω
  intro t ht
  rw [hω t ht]
  simp only [inner_sum]
  unfold finiteJumpGain
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : M.times k ω ≤ t <;> simp [h]

/-- The same price identity holds at an arbitrary stopped time, including its
jump, on one common probability-one set. -/
theorem PriceJumpModel.stopped_constant_gain_representation
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (v : V) (σ : Ω → NNReal) :
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      finiteJumpGain M.active M.times M.marks (stoppedStrategy (fun _ => v) σ) t ω =
        inner ℝ v (S (min t (σ ω)) ω - S 0 ω) := by
  filter_upwards [M.constant_gain_representation v] with ω hω
  intro t ht
  rw [finite_gain_stopped]
  exact hω _ ((min_le_left _ _).trans ht)

/-- Deterministically bounded stopped prices make each constant stopped test
portfolio admissible. This applies to both signs of every coordinate vector. -/
theorem PriceJumpModel.admissible_stopped_constant
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (v : V) (σ : Ω → NNReal)
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ‖S 0 ω‖ ≤ b ∧ ∀ t ≤ T, ‖S (min t (σ ω)) ω‖ ≤ b) :
    AdmissibleStrategy P 𝓕 M.active M.times M.marks T
      (stoppedStrategy (fun _ => v) σ) := by
  refine ⟨stopped_strategy_predictable 𝓕 _ measurable_const σ hσ,
    2 * ‖v‖ * b + 1, by positivity, ?_⟩
  filter_upwards [M.stopped_constant_gain_representation v σ, hbound] with ω hω hB
  intro t ht
  rw [hω t ht]
  have hn : ‖S (min t (σ ω)) ω - S 0 ω‖ ≤ 2 * b :=
    (norm_sub_le _ _).trans (by linarith [hB.1, hB.2 t ht])
  have hi := abs_real_inner_le_norm v (S (min t (σ ω)) ω - S 0 ω)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
  have hl := neg_abs_le (inner ℝ v (S (min t (σ ω)) ω - S 0 ω))
  nlinarith

#print axioms PriceJumpModel.constant_gain_representation
#print axioms PriceJumpModel.stopped_constant_gain_representation
#print axioms PriceJumpModel.admissible_stopped_constant
end FTDAP
