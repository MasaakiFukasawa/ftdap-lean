import PredictableStoppedMarks

open MeasureTheory Set
namespace FTDAP
variable {Ω ι V : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [InnerProductSpace ℝ V] in
/-- Predictable holdings evaluated at a stopping time are measurable at that time. -/
theorem predictable_portfolio_stopped_measurable (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (τ : Ω → ι) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι)))
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H) :
    Measurable[hτ.measurableSpace] (fun ω => H (τ ω, ω)) := by
  have hp : IsStronglyPredictable 𝓕 (fun t ω => H (t, ω)) := hH.stronglyMeasurable
  have hm := measurable_stoppedValue hp.isStronglyProgressive hτ
  simpa [stoppedValue] using hm

/-- Predictability of pre-jump wealth is derived from stopping-time measurable
increments and active-jump events, rather than imposed on the wealth process. -/
theorem pre_jump_wealth_predictable [DenselyOrdered ι]
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (hτ : ∀ k, IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ι)))
    (Δ : ℕ → Ω → V)
    (hΔ : ∀ k, Measurable[(hτ k).measurableSpace] (Δ k))
    (hactive : ∀ k, MeasurableSet[(hτ k).measurableSpace] {ω | k ∈ jumps ω})
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H) (a : ℝ) :
    Measurable[𝓕.predictable] (fun p : ι × Ω => a + preJumpGain jumps τ Δ H p.1 p.2) := by
  classical
  have hmark : ∀ k, Measurable[(hτ k).measurableSpace]
      (fun ω => if k ∈ jumps ω then inner ℝ (H (τ k ω, ω)) (Δ k ω) else 0) := by
    intro k
    have hhold := predictable_portfolio_stopped_measurable 𝓕 (τ k) (hτ k) H hH
    have hi : Measurable[(hτ k).measurableSpace]
        (fun ω => inner ℝ (H (τ k ω, ω)) (Δ k ω)) :=
      continuous_inner.measurable.comp (hhold.prodMk (hΔ k))
    exact hi.ite (hactive k) measurable_const
  exact measurable_const.add (predictable_pre_jump_gain 𝓕 jumps τ hτ Δ H hmark)

#print axioms predictable_portfolio_stopped_measurable
#print axioms pre_jump_wealth_predictable
end FTDAP
