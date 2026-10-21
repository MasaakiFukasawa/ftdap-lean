import AlmostSureTrading
import TradingCone

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω ι V : Type*} [LinearOrder ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Retain every trade through the stopping time, including a jump at that time. -/
noncomputable def stoppedStrategy (H : ι × Ω → V) (σ : Ω → ι) (p : ι × Ω) : V :=
  if p.1 ≤ σ p.2 then H p else 0

/-- Stopping the holdings, including the stopping jump, stops the finite gain. -/
theorem finite_gain_stopped (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (σ : Ω → ι) (t : ι) (ω : Ω) :
    finiteJumpGain jumps τ Δ (stoppedStrategy H σ) t ω =
      finiteJumpGain jumps τ Δ H (min t (σ ω)) ω := by
  unfold finiteJumpGain
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : τ k ω ≤ t <;> by_cases hs : τ k ω ≤ σ ω <;>
    simp [stoppedStrategy, ht, hs]

variable [MeasurableSpace Ω] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
  [BorelSpace ι] [OrderTopology ι] [SecondCountableTopology ι] [DenselyOrdered ι]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [InnerProductSpace ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- Arbitrary stopping times preserve predictability of stopped holdings. -/
theorem stopped_strategy_predictable (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H) (σ : Ω → ι)
    (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ι))) :
    Measurable[𝓕.predictable] (stoppedStrategy H σ) := by
  exact hH.ite (predictable_stopped_interval 𝓕 σ hσ) measurable_const

omit [BorelSpace V] [SecondCountableTopology V] in
/-- The same deterministic lower bound works after stopping a portfolio. -/
theorem admissible_stopped_strategy
    (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (H : ι × Ω → V) (hH : AdmissibleStrategy P 𝓕 jumps τ Δ T H)
    (σ : Ω → ι) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ι))) :
    AdmissibleStrategy P 𝓕 jumps τ Δ T (stoppedStrategy H σ) := by
  obtain ⟨hpred, b, hb, hlower⟩ := hH
  refine ⟨stopped_strategy_predictable 𝓕 H hpred σ hσ, b, hb, ?_⟩
  filter_upwards [hlower] with ω hω
  intro t ht
  rw [finite_gain_stopped]
  exact hω _ ((min_le_left _ _).trans ht)

#print axioms finite_gain_stopped
#print axioms stopped_strategy_predictable
#print axioms admissible_stopped_strategy
end FTDAP
