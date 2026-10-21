import ConverseFTAP
import ForwardFTAP

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- Equivalent versions of the source price have the same jump trading model. -/
def PriceJumpModel.congr_prices
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S R : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (he : ∀ᵐ ω ∂P, ∀ t ≤ T, R t ω = S t ω) : PriceJumpModel P 𝓕 R T where
  active := M.active
  times := M.times
  marks := M.marks
  stopping := M.stopping
  measurable_marks := M.measurable_marks
  measurable_active := M.measurable_active
  injective_times := M.injective_times
  bounds := M.bounds
  representation := by
    filter_upwards [M.representation, he] with ω hω heω
    intro t ht
    rw [heω t ht, heω 0 bot_le]
    exact hω t ht

/-- Absolute continuity transports the representation to a new measure. -/
def PriceJumpModel.change_measure
    {P Q : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (hQP : Q ≪ P) : PriceJumpModel Q 𝓕 S T where
  active := M.active
  times := M.times
  marks := M.marks
  stopping := M.stopping
  measurable_marks := M.measurable_marks
  measurable_active := M.measurable_active
  injective_times := M.injective_times
  bounds := M.bounds
  representation := hQP.ae_le M.representation

variable [InnerProductSpace ℝ V]

/-- NA is invariant under equivalent probability measures. -/
theorem gain_na_of_equivalent_measure
    {P Q : Measure Ω} (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → NNReal) (Δ : ℕ → Ω → V) (T : NNReal)
    (hna : GainNoArbitrage Q 𝓕 jumps τ Δ T) : GainNoArbitrage P 𝓕 jumps τ Δ T := by
  intro H hH hadm hnonneg
  obtain ⟨a, ha, hb⟩ := hadm
  exact hPQ.ae_le (hna H hH ⟨a, ha, hQP.ae_le hb⟩ (hQP.ae_le hnonneg))

#print axioms gain_na_of_equivalent_measure
end FTDAP
