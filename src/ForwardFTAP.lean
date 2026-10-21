import TradingConeClosed
import LocalMartingaleFromSeparator

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The forward FTAP implication for the constructed price-jump trading model:
NA, locally finite price states and bounded-price localizers give an equivalent
local martingale measure, with every closure and separation step derived. -/
theorem PriceJumpModel.na_implies_equivalent_local_martingale_measure
    [FiniteDimensional ℝ V] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω)) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (hna : GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hstates : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (σ n ω : WithTop NNReal)))
    (hmon : ∀ ω, Monotone (fun n => σ n ω))
    (hterm : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, σ n ω = T)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ n ω) : NNReal) : ℝ) ω‖ ≤ b n) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T := by
  have hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E :=
    hstates.mono (fun ω hω => ⟨hcad ω, hω⟩)
  have hcover : ∀ᵐ ω ∂P, ∃ m, T ≤ σ m ω := by
    filter_upwards [hterm] with ω hω
    obtain ⟨N, hN⟩ := hω
    exact ⟨N, (hN N le_rfl).ge⟩
  have hclosed := M.trading_cone_closed_from_prices (nonnegativeFiltration 𝓕) S T E hE hpath
    σ hσ hcover b hbound hna
  exact M.equivalent_local_martingale_measure_of_closed_cone 𝓕 S hadapt hcad T hna hclosed
    σ hσ hmon hterm b hb hbound

#print axioms PriceJumpModel.na_implies_equivalent_local_martingale_measure
end FTDAP
