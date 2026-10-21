import CompactPriceExtension
import BoundedPriceFTAP

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- The price assumptions stated directly on the compact time interval. -/
structure CompactPriceHypotheses (P : Measure Ω) (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (T : NNReal) (S : Icc (0 : ℝ) (T : ℝ) → Ω → V) where
  adapted : ∀ t, Measurable[𝓕 t.val] (S t)
  initial : V
  states : Set V
  locally_finite : ∀ B : Set V, Bornology.IsBounded B → (states ∩ B).Finite
  paths : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧
    S ⟨0, ⟨le_rfl, T.property⟩⟩ ω = initial ∧ ∀ t, S t ω ∈ states
  localizers : ℕ → Ω → NNReal
  stopping : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
    (fun ω => (localizers n ω : WithTop NNReal))
  increasing : ∀ ω, Monotone (fun n => localizers n ω)
  eventually_horizon : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, localizers n ω = T
  bound : ℕ → ℝ
  bound_nonneg : ∀ n, 0 ≤ bound n
  bounded_stops : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
    ‖S (horizonClamp T ((min t (localizers n ω) : NNReal) : ℝ)) ω‖ ≤ bound n

/-- Extending the compact process meets all real-indexed source assumptions;
there is no regularity or measurability premise outside the original horizon. -/
def CompactPriceHypotheses.toSource
    {P : Measure Ω} {𝓕 : Filtration ℝ ‹MeasurableSpace Ω›} {T : NNReal}
    {S : Icc (0 : ℝ) (T : ℝ) → Ω → V} (h : CompactPriceHypotheses P 𝓕 T S) :
    SourcePriceHypotheses P 𝓕 (compactPriceExtension T S h.initial) T where
  adapted := compactPriceExtension_adapted 𝓕 T S h.initial h.adapted
  initial := h.initial
  states := h.states
  locally_finite := h.locally_finite
  paths := by
    filter_upwards [h.paths] with ω hω
    refine ⟨cadlag_constant_before_zero _ (cadlag_compact_horizon_extension T _ hω.1)
      h.initial, ?_, ?_⟩
    · rw [compactPriceExtension_value T S h.initial ⟨0, ⟨le_rfl, T.property⟩⟩]
      exact hω.2.1
    · intro t ht
      have he := congrFun (compactPriceExtension_value T S h.initial ⟨t, ht⟩) ω
      exact he ▸ hω.2.2 ⟨t, ht⟩
  localizers := h.localizers
  stopping := h.stopping
  increasing := h.increasing
  eventually_horizon := h.eventually_horizon
  bound := h.bound
  bound_nonneg := h.bound_nonneg
  bounded_stops := by
    intro n
    filter_upwards [h.bounded_stops n] with ω hω
    intro t ht
    change ‖if ((min t (h.localizers n ω) : NNReal) : ℝ) < 0 then h.initial
      else S (horizonClamp T ((min t (h.localizers n ω) : NNReal) : ℝ)) ω‖ ≤ h.bound n
    split_ifs with hh
    · exact False.elim ((not_lt_of_ge (min t (h.localizers n ω)).property) hh)
    · exact hω t ht

variable [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [BorelSpace V] [SecondCountableTopology V]

/-- The full FTAP for a process originally defined only on [0,T]. The explicit
extension agrees with that process at every horizon time. -/
theorem compact_horizon_ftap
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (T : NNReal) (S : Icc (0 : ℝ) (T : ℝ) → Ω → V)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (h : CompactPriceHypotheses P 𝓕 T S) :
    let R := compactPriceExtension T S h.initial
    ∃ M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => R (t : ℝ)) T,
      let NA := GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
      let C := tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T
      (NA ↔ ConeNFLVR P C) ∧ (NA ↔ ConeNFL P C) ∧
        (NA ↔ ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
          HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => R (t : ℝ)) T) ∧
        (NA → IsClosed C) :=
  source_price_ftap_with_constructed_model 𝓕 _ T hcomplete h.toSource

/-- The bounded-price assertion for a process given only on the compact horizon. -/
theorem compact_horizon_bounded_ftap
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (T : NNReal)
    (S : Icc (0 : ℝ) (T : ℝ) → Ω → V)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (h : CompactPriceHypotheses P 𝓕 T S)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕)
      (fun t => compactPriceExtension T S h.initial (t : ℝ)) T)
    (hna : GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T)
    (b : ℝ) (hb : ∀ᵐ ω ∂P, ∀ t, ‖S t ω‖ ≤ b) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      Martingale (fun (t : Iic T) ω => S (horizonClamp T (t.val : ℝ)) ω)
        (horizonFiltration (nonnegativeFiltration 𝓕) T) Q := by
  have hbound : ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖compactPriceExtension T S h.initial (t : ℝ) ω‖ ≤ b := by
    filter_upwards [hb] with ω hω
    intro t _ht
    change ‖if (t : ℝ) < 0 then h.initial else S (horizonClamp T t) ω‖ ≤ b
    split_ifs with hh
    · exact False.elim ((not_lt_of_ge t.property) hh)
    · exact hω _
  obtain ⟨Q, hQ, hQP, hPQ, hm⟩ := M.bounded_source_price_ftap 𝓕 _ T hcomplete h.toSource hna b hbound
  refine ⟨Q, hQ, hQP, hPQ, ?_⟩
  have he : (fun (t : Iic T) ω => compactPriceExtension T S h.initial (t.val : ℝ) ω) =
      (fun (t : Iic T) ω => S (horizonClamp T (t.val : ℝ)) ω) := by
    funext t ω
    change (if (t.val : ℝ) < 0 then h.initial else S (horizonClamp T t.val) ω) = _
    exact ite_eq_right (not_lt.mpr t.val.property)
  rw [he] at hm
  exact hm

#print axioms compact_horizon_bounded_ftap
#print axioms CompactPriceHypotheses.toSource
#print axioms compact_horizon_ftap
end FTDAP
