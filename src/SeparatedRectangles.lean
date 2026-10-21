import SeparatedGains

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Rectangle payoffs are bounded claims whenever the stopped prices are bounded. -/
theorem PriceJumpModel.rectangle_gain_bounded
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (v : V) (σ : Ω → NNReal) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖S (min t (σ ω)) ω‖ ≤ b)
    (s t : NNReal) (hst : s ≤ t) (ht : t ≤ T) (A : Set Ω) :
    ∀ᵐ ω ∂P, |finiteJumpGain M.active M.times M.marks
      (priceRectangleStrategy v σ s t A) T ω| ≤ 2 * ‖v‖ * b := by
  classical
  filter_upwards [M.rectangle_gain_representation v σ s t hst ht A, hbound] with ω hω hB
  rw [hω]
  by_cases ha : ω ∈ A
  · rw [ite_eq_left ha]
    have hn : ‖S (min t (σ ω)) ω - S (min s (σ ω)) ω‖ ≤ 2 * b :=
      (norm_sub_le _ _).trans (by linarith [hB t ht, hB s (hst.trans ht)])
    have hi := abs_real_inner_le_norm v (S (min t (σ ω)) ω - S (min s (σ ω)) ω)
    have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg v)
    nlinarith
  · rw [ite_eq_right ha, abs_zero]
    positivity

/-- A separator of the actual bounded-claim trading cone gives zero stopped
price rectangle tests. No expected-gain premise is assumed. -/
theorem PriceJumpModel.rectangle_tests_of_separator
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (Z : Lp ℝ 1 P) (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hsep : ∀ f ∈ tradingCone P 𝓕 M.active M.times M.marks T, claimsPairing P f Z ≤ 0)
    (v : V) (σ : Ω → NNReal)
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ‖S 0 ω‖ ≤ b ∧ ∀ t ≤ T, ‖S (min t (σ ω)) ω‖ ≤ b)
    (s t : NNReal) (hst : s ≤ t) (ht : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A, inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω)
      ∂P.withDensity (fun ω => ENNReal.ofReal (Z ω))) = 0 := by
  classical
  let Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  have hm : ∀ w : V, (∫ ω, if ω ∈ A then
      inner ℝ w (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0 ∂Q) ≤ 0 := by
    intro w
    have ha := M.rectangle_admissible w σ hσ b hb hbound s t A hA
    have hB := M.rectangle_gain_bounded w σ b hb (hbound.mono (fun _ h => h.2)) s t hst ht A
    have he := hQP.ae_eq (M.rectangle_gain_representation w σ s t hst ht A)
    rw [← integral_congr_ae he]
    exact M.bounded_gain_separated Z hZ hsep _ ha _ hB
  have hp := hm v
  have hn := hm (-v)
  have he : (fun ω => if ω ∈ A then
      inner ℝ (-v) (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0) =
      fun ω => -(if ω ∈ A then
        inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0) := by
    funext ω
    by_cases ha : ω ∈ A <;> simp [ha]
  rw [he, integral_neg] at hn
  have hz : (∫ ω, if ω ∈ A then
      inner ℝ v (S (min t (σ ω)) ω - S (min s (σ ω)) ω) else 0 ∂Q) = 0 := by linarith
  rw [← integral_indicator ((𝓕.le s) A hA)]
  exact hz

#print axioms PriceJumpModel.rectangle_gain_bounded
#print axioms PriceJumpModel.rectangle_tests_of_separator
end FTDAP
