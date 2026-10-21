import StoppedJumpModel

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Localized bounded variation and the martingale property give the expected
wealth inequality for every admissible predictable strategy. -/
theorem PriceJumpModel.admissible_gain_nonpos_of_localized_variation
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : WithTop NNReal)))
    (hevent : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, σ n ω = T)
    (hmart : ∀ n, Martingale (fun (t : Iic T) ω => S (min t.val (σ n ω)) ω)
      (horizonFiltration 𝓕 T) P)
    (K : ℕ → ℝ)
    (hvar : ∀ n, ∀ᵐ ω ∂P,
      (∑ k ∈ (M.stop (σ n) (hσ n)).active ω, ‖M.marks k ω‖) ≤ K n)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H) (a : ℝ)
    (hadm : ∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks H t ω) :
    Integrable (finiteJumpGain M.active M.times M.marks H T) P ∧
      (∫ ω, finiteJumpGain M.active M.times M.marks H T ω ∂P) ≤ 0 := by
  let Y := fun n => finiteJumpGain (M.stop (σ n) (hσ n)).active
    (M.stop (σ n) (hσ n)).times (M.stop (σ n) (hσ n)).marks H T
  have hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t ≤ T,
      -a ≤ finiteJumpGain (M.stop (σ n) (hσ n)).active
        (M.stop (σ n) (hσ n)).times (M.stop (σ n) (hσ n)).marks H t ω := by
    intro n
    filter_upwards [hadm] with ω hω
    intro t ht
    rw [M.stopped_model_gain]
    exact hω _ ((min_le_left _ _).trans ht)
  have hy := fun n => (M.stop (σ n) (hσ n)).admissible_gain_nonpos_of_bounded_variation
    (hmart n) (K n) (hvar n) H hH a (hbound n)
  apply localized_wealth_fatou P Y _ (fun n => (hy n).1) (fun n => (hy n).2) a
  · exact fun n => (hbound n).mono (fun _ h => h T le_rfl)
  · filter_upwards [hevent] with ω hω
    have he : (fun n => Y n ω) =ᶠ[atTop]
        (fun _ => finiteJumpGain M.active M.times M.marks H T ω) := by
      filter_upwards [hω] with n hn
      dsimp [Y]
      rw [M.stopped_model_gain, hn, min_self]
    exact tendsto_const_nhds.congr' he.symm

/-- A localized finite-jump martingale satisfies NA for arbitrary admissible
holdings when its localized total jump variations have deterministic bounds. -/
theorem PriceJumpModel.no_arbitrage_of_localized_variation
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : WithTop NNReal)))
    (hevent : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, σ n ω = T)
    (hmart : ∀ n, Martingale (fun (t : Iic T) ω => S (min t.val (σ n ω)) ω)
      (horizonFiltration 𝓕 T) P)
    (K : ℕ → ℝ)
    (hvar : ∀ n, ∀ᵐ ω ∂P,
      (∑ k ∈ (M.stop (σ n) (hσ n)).active ω, ‖M.marks k ω‖) ≤ K n) :
    GainNoArbitrage P 𝓕 M.active M.times M.marks T := by
  intro H hH hadm hnonneg
  obtain ⟨a, _ha, hbound⟩ := hadm
  obtain ⟨hint, hmean⟩ := M.admissible_gain_nonpos_of_localized_variation
    σ hσ hevent hmart K hvar H hH a hbound
  have hz : (∫ ω, finiteJumpGain M.active M.times M.marks H T ω ∂P) = 0 :=
    le_antisymm hmean (integral_nonneg_of_ae hnonneg)
  exact (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hz

#print axioms PriceJumpModel.admissible_gain_nonpos_of_localized_variation
#print axioms PriceJumpModel.no_arbitrage_of_localized_variation
end FTDAP
