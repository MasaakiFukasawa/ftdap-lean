import TruncatedHoldings
import Fatou

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Bounded total jump variation plus the martingale property rules out
positive expected admissible gains, even for unbounded predictable holdings. -/
theorem PriceJumpModel.admissible_gain_nonpos_of_bounded_variation
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (hmart : Martingale (fun (t : Iic T) => S t.val) (horizonFiltration 𝓕 T) P)
    (K : ℝ) (hvar : ∀ᵐ ω ∂P, (∑ k ∈ M.active ω, ‖M.marks k ω‖) ≤ K)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H) (a : ℝ)
    (hadm : ∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks H t ω) :
    Integrable (finiteJumpGain M.active M.times M.marks H T) P ∧
      (∫ ω, finiteJumpGain M.active M.times M.marks H T ω ∂P) ≤ 0 := by
  let Y := fun (n : ℕ) => finiteJumpGain M.active M.times M.marks (M.truncatedHoldings H (n : ℝ)) T
  have htrunc := fun n : ℕ => M.truncatedHoldings_predictable_bound H hH (n : ℝ) (Nat.cast_nonneg n)
  have hz := fun n : ℕ => M.bounded_variation_gain hmart K hvar (M.truncatedHoldings H (n : ℝ))
    (htrunc n).1 (n : ℝ) (Nat.cast_nonneg n) (htrunc n).2
  apply localized_wealth_fatou P Y _ (fun n => (hz n).1) (fun n => (hz n).2.le) a
  · intro n
    filter_upwards [hadm] with ω hω
    exact M.truncated_gain_lower_bound H (n : ℝ) a ω hω T le_rfl
  · exact Eventually.of_forall (fun ω => by
      obtain ⟨N, hN⟩ := M.truncated_gains_eventually_equal H ω
      have he : (fun n => Y n ω) =ᶠ[atTop]
          (fun _ => finiteJumpGain M.active M.times M.marks H T ω) :=
        eventually_atTop.mpr ⟨N, fun n hn => hN n hn T⟩
      exact tendsto_const_nhds.congr' he.symm)

/-- A martingale with bounded total jump variation satisfies NA for all
predictable admissible portfolios. -/
theorem PriceJumpModel.no_arbitrage_of_bounded_variation_martingale
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (hmart : Martingale (fun (t : Iic T) => S t.val) (horizonFiltration 𝓕 T) P)
    (K : ℝ) (hvar : ∀ᵐ ω ∂P, (∑ k ∈ M.active ω, ‖M.marks k ω‖) ≤ K) :
    GainNoArbitrage P 𝓕 M.active M.times M.marks T := by
  intro H hH hadm hnonneg
  obtain ⟨a, _ha, hbound⟩ := hadm
  obtain ⟨hint, hmean⟩ := M.admissible_gain_nonpos_of_bounded_variation hmart K hvar H hH a hbound
  have hzero : (∫ ω, finiteJumpGain M.active M.times M.marks H T ω ∂P) = 0 :=
    le_antisymm hmean (integral_nonneg_of_ae hnonneg)
  exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero

#print axioms PriceJumpModel.admissible_gain_nonpos_of_bounded_variation
#print axioms PriceJumpModel.no_arbitrage_of_bounded_variation_martingale
end FTDAP
