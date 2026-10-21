import JumpMeasure
import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.MetricSpace.Polish

open MeasureTheory Set
namespace FTDAP
set_option linter.unusedSectionVars false
variable {Ω ι : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [OrderClosedTopology ι]

/-- The predictable sigma algebra is contained in the full time/sample product sigma algebra. -/
theorem predictable_le_product (𝓕 : Filtration ι ‹MeasurableSpace Ω›) :
    𝓕.predictable ≤ (inferInstance : MeasurableSpace (ι × Ω)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton _).prod (𝓕.le ⊥ A hA)
  · intro i A hA
    exact measurableSet_Ioi.prod (𝓕.le i A hA)

/-- Evaluating a predictable set at a measurable random time is measurably legitimate.
This supplies the random-atom measurability needed by jumpMeasure. -/
theorem measurable_predictable_atom (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (τ : Ω → ι) (hτ : Measurable τ) :
    @Measurable Ω (ι × Ω) ‹MeasurableSpace Ω› 𝓕.predictable
      (fun ω => (τ ω, ω)) := by
  exact (hτ.prodMk measurable_id).mono le_rfl (predictable_le_product 𝓕)

/-- [0,τ] is predictable for an arbitrary stopping time, including its graph. -/
theorem predictable_stopped_interval [SecondCountableTopology ι] [OrderTopology ι]
    [DenselyOrdered ι] (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (τ : Ω → ι) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι))) :
    MeasurableSet[𝓕.predictable] {p : ι × Ω | p.1 ≤ τ p.2} := by
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense ι
  have heq : {p : ι × Ω | τ p.2 < p.1} =
      ⋃ q ∈ D, Ioi q ×ˢ {ω | τ ω ≤ q} := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hqD, hqτ, hqt⟩ := hdense.exists_between hp
      exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hqD, hqt, hqτ.le⟩⟩
    · intro hp
      obtain ⟨q, hq⟩ := mem_iUnion.mp hp
      obtain ⟨hqD, hqt, hqτ⟩ := mem_iUnion.mp hq
      exact hqτ.trans_lt hqt
  have hgt : MeasurableSet[𝓕.predictable] {p : ι × Ω | τ p.2 < p.1} := by
    rw [heq]
    exact MeasurableSet.biUnion hD (fun q hq => measurableSet_predictable_Ioi_prod (by simpa using hτ q))
  have hc := hgt.compl
  simpa only [compl_ofPred, not_lt] using hc

/-- The random intervals used to assemble the strategy-independent constants. -/
theorem predictable_localizing_interval [SecondCountableTopology ι] [OrderTopology ι]
    [DenselyOrdered ι] (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (σ τ : Ω → ι) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ι))) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι))) :
    MeasurableSet[𝓕.predictable] {p : ι × Ω | σ p.2 < p.1 ∧ p.1 ≤ τ p.2} := by
  have hleft := (predictable_stopped_interval 𝓕 σ hσ).compl
  have hright := predictable_stopped_interval 𝓕 τ hτ
  simpa only [compl_ofPred, not_le, ofPred_and] using hleft.inter hright

#print axioms measurable_predictable_atom
#print axioms predictable_stopped_interval
end FTDAP
