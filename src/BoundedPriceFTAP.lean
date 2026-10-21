import SourceFTAP
import BoundedLocalMartingale

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The bounded-price conclusion of the manuscript's FTAP. -/
theorem PriceJumpModel.bounded_source_price_ftap
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V) (T : NNReal)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (h : SourcePriceHypotheses P 𝓕 S T)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (hna : GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T)
    (b : ℝ) (hbound : ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T → ‖S (t : ℝ) ω‖ ≤ b) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      Martingale (fun (t : Iic T) ω => S (t.val : ℝ) ω)
        (horizonFiltration (nonnegativeFiltration 𝓕) T) Q := by
  obtain ⟨Q, hQ, hQP, hPQ, hlm⟩ := (M.source_price_ftap 𝓕 S T hcomplete h).2.2.1.mp hna
  let := hQ
  exact ⟨Q, hQ, hQP, hPQ, bounded_horizon_local_martingale hlm
    (fun t => (h.adapted (t.val : ℝ)).stronglyMeasurable) b (hQP.ae_le hbound)⟩

#print axioms PriceJumpModel.bounded_source_price_ftap
end FTDAP
