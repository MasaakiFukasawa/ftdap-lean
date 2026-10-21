import PriceTestStrategies

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A bounded gain can be continued on an event known at the starting time. -/
theorem continued_admissible_of_abs_bound
    (P : Measure Ω) (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → NNReal) (Δ : ℕ → Ω → V) (T : NNReal)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H)
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, |finiteJumpGain jumps τ Δ H t ω| ≤ b)
    (s : NNReal) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    AdmissibleStrategy P 𝓕 jumps τ Δ T (continuedStrategy H s A) := by
  refine ⟨continued_strategy_predictable 𝓕 H hH s A hA, 2*b+1, by positivity, ?_⟩
  filter_upwards [hbound] with ω hω
  intro t ht
  by_cases hst : s ≤ t
  · rw [continued_gain_after jumps τ Δ H s t A hst]
    by_cases ha : ω ∈ A
    · rw [ite_eq_left ha]
      have ht' := (abs_le.mp (hω t ht)).1
      have hs' := (abs_le.mp (hω s (hst.trans ht))).2
      linarith
    · rw [ite_eq_right ha]
      linarith
  · rw [continued_gain_before jumps τ Δ H s t A (le_of_not_ge hst)]
    linarith

/-- Hold v only on A, after s and through t, and stop at the price localizer. -/
noncomputable def priceRectangleStrategy (v : V) (σ : Ω → NNReal)
    (s t : NNReal) (A : Set Ω) : NNReal × Ω → V :=
  stoppedStrategy (continuedStrategy (stoppedStrategy (fun _ => v) σ) s A) (fun _ => t)

omit [BorelSpace V] in
/-- The terminal rectangle gain is exactly the event-restricted stopped-price
increment, which supplies the scalar martingale tests. -/
theorem PriceJumpModel.rectangle_gain_representation
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (v : V) (σ : Ω → NNReal) (s t : NNReal) (hst : s ≤ t) (ht : t ≤ T) (A : Set Ω) :
    ∀ᵐ ω ∂P,
      finiteJumpGain M.active M.times M.marks (priceRectangleStrategy v σ s t A) T ω =
        if ω ∈ A then inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0 := by
  filter_upwards [M.stopped_constant_gain_representation v σ] with ω hω
  unfold priceRectangleStrategy
  rw [finite_gain_stopped, min_eq_right ht,
    continued_gain_after M.active M.times M.marks _ s t A hst,
    hω t ht, hω s (hst.trans ht)]
  by_cases ha : ω ∈ A
  · simp only [ite_eq_left ha, inner_sub_right]
    ring
  · simp only [ite_eq_right ha]

/-- Both signs of each rectangle test are admissible for bounded stopped prices. -/
theorem PriceJumpModel.rectangle_admissible
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (v : V) (σ : Ω → NNReal)
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ‖S 0 ω‖ ≤ b ∧ ∀ t ≤ T, ‖S (min t (σ ω)) ω‖ ≤ b)
    (s t : NNReal) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    AdmissibleStrategy P 𝓕 M.active M.times M.marks T (priceRectangleStrategy v σ s t A) := by
  have hbase : Measurable[𝓕.predictable] (stoppedStrategy (fun _ => v) σ) :=
    stopped_strategy_predictable 𝓕 _ measurable_const σ hσ
  have hB : ∀ᵐ ω ∂P, ∀ u ≤ T,
      |finiteJumpGain M.active M.times M.marks (stoppedStrategy (fun _ => v) σ) u ω| ≤
        2 * ‖v‖ * b := by
    filter_upwards [M.stopped_constant_gain_representation v σ, hbound] with ω hω hboundω
    intro u hu
    rw [hω u hu]
    have hn : ‖S (min u (σ ω)) ω - S 0 ω‖ ≤ 2 * b :=
      (norm_sub_le _ _).trans (by linarith [hboundω.1, hboundω.2 u hu])
    have hi := abs_real_inner_le_norm v (S (min u (σ ω)) ω - S 0 ω)
    have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
    nlinarith
  have hcont := continued_admissible_of_abs_bound P 𝓕 M.active M.times M.marks T
    _ hbase (2 * ‖v‖ * b) (by positivity) hB s A hA
  exact admissible_stopped_strategy P 𝓕 M.active M.times M.marks T _ hcont
    (fun _ => t) (isStoppingTime_const 𝓕 t)

/-- Nonpositive means of all admissible gains force zero stopped-price
rectangle tests. The mean inequality is the separator property that must still
be obtained from the closed trading cone. -/
theorem PriceJumpModel.rectangle_tests_of_gain_inequality
    {P Q : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (hQP : Q ≪ P)
    (hsep : ∀ H, AdmissibleStrategy P 𝓕 M.active M.times M.marks T H →
      (∫ ω, finiteJumpGain M.active M.times M.marks H T ω ∂Q) ≤ 0)
    (v : V) (σ : Ω → NNReal)
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ‖S 0 ω‖ ≤ b ∧ ∀ t ≤ T, ‖S (min t (σ ω)) ω‖ ≤ b)
    (s t : NNReal) (hst : s ≤ t) (ht : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A, inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω) ∂Q) = 0 := by
  have htest : ∀ w : V, (∫ ω, if ω ∈ A then
      inner ℝ w (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0 ∂Q) ≤ 0 := by
    intro w
    have ha := M.rectangle_admissible w σ hσ b hb hbound s t A hA
    have he := hQP.ae_eq (M.rectangle_gain_representation w σ s t hst ht A)
    rw [← integral_congr_ae he]
    exact hsep _ ha
  have hp := htest v
  have hn := htest (-v)
  have he : (fun ω => if ω ∈ A then
      inner ℝ (-v) (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0) =
      fun ω => -(if ω ∈ A then
        inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0) := by
    funext ω
    by_cases ha : ω ∈ A <;> simp [ha]
  rw [he, integral_neg] at hn
  have hz : (∫ ω, if ω ∈ A then
      inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0 ∂Q) = 0 := by
    linarith
  have hAm : MeasurableSet A := (𝓕.le s) A hA
  rw [← integral_indicator hAm]
  exact hz

#print axioms PriceJumpModel.rectangle_tests_of_gain_inequality
#print axioms continued_admissible_of_abs_bound
#print axioms PriceJumpModel.rectangle_gain_representation
#print axioms PriceJumpModel.rectangle_admissible
end FTDAP
