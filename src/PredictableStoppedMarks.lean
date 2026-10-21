import PredictableAtoms
import PreJumpWealth
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory Set TopologicalSpace
namespace FTDAP
variable {Ω ι V : Type*} [MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [OrderClosedTopology ι]
    [SecondCountableTopology ι] [OrderTopology ι] [DenselyOrdered ι]
    [MeasurableSpace V] [Zero V]

/-- A mark measurable at a stopping time is predictable strictly after that time. -/
theorem predictable_stopped_mark (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (τ : Ω → ι) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι)))
    (Z : Ω → V) (hZ : Measurable[hτ.measurableSpace] Z) :
    Measurable[𝓕.predictable] (fun p : ι × Ω => if τ p.2 < p.1 then Z p.2 else 0) := by
  classical
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense ι
  have hcover : MeasurableSet[𝓕.predictable] {p : ι × Ω | τ p.2 < p.1} := by
    simpa only [compl_ofPred, not_le] using (predictable_stopped_interval 𝓕 τ hτ).compl
  intro A hA
  have hmark : MeasurableSet[𝓕.predictable]
      {p : ι × Ω | τ p.2 < p.1 ∧ Z p.2 ∈ A} := by
    have he : {p : ι × Ω | τ p.2 < p.1 ∧ Z p.2 ∈ A} =
        ⋃ q ∈ D, Ioi q ×ˢ ((Z ⁻¹' A) ∩ {ω | τ ω ≤ q}) := by
      ext p
      constructor
      · intro hp
        obtain ⟨q, hqD, hqτ, hqt⟩ := hdense.exists_between hp.1
        exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hqD, hqt, hp.2, hqτ.le⟩⟩
      · intro hp
        obtain ⟨q, hq⟩ := mem_iUnion.mp hp
        obtain ⟨_, hqt, hZA, hτq⟩ := mem_iUnion.mp hq
        exact ⟨hτq.trans_lt hqt, hZA⟩
    rw [he]
    apply MeasurableSet.biUnion hD
    intro q _
    apply measurableSet_predictable_Ioi_prod
    have hstop := (hτ.measurableSet (Z ⁻¹' A)).mp (hZ hA)
    simpa using hstop.2 q
  have he : (fun p : ι × Ω => if τ p.2 < p.1 then Z p.2 else 0) ⁻¹' A =
      {p : ι × Ω | τ p.2 < p.1 ∧ Z p.2 ∈ A} ∪
        (if (0 : V) ∈ A then {p : ι × Ω | τ p.2 < p.1}ᶜ else ∅) := by
    ext p
    by_cases ht : τ p.2 < p.1 <;> by_cases hz : (0 : V) ∈ A <;> simp [ht, hz]
  rw [he]
  apply hmark.union
  split_ifs
  · exact hcover.compl
  · exact @MeasurableSet.empty (ι × Ω) 𝓕.predictable

/-- Countably many stopped marks give a predictable pre-jump sum. -/
theorem predictable_pre_jump_sum (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (τ : ℕ → Ω → ι)
    (hτ : ∀ k, IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ι)))
    (Z : ℕ → Ω → ℝ) (hZ : ∀ k, Measurable[(hτ k).measurableSpace] (Z k)) :
    Measurable[𝓕.predictable]
      (fun p : ι × Ω => ∑' k, if τ k p.2 < p.1 then Z k p.2 else 0) := by
  let : MeasurableSpace (ι × Ω) := 𝓕.predictable
  exact Measurable.tsum (fun k => predictable_stopped_mark 𝓕 (τ k) (hτ k) (Z k) (hZ k))

omit [MeasurableSpace V] [Zero V] in
/-- The actual finite pre-jump gain is predictable when its inactive-inclusive
jump marks are measurable at the enumerated stopping times. -/
theorem predictable_pre_jump_gain {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (hτ : ∀ k, IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ι)))
    (Δ : ℕ → Ω → W) (H : ι × Ω → W)
    (hmark : ∀ k, Measurable[(hτ k).measurableSpace]
      (fun ω => if k ∈ jumps ω then inner ℝ (H (τ k ω, ω)) (Δ k ω) else 0)) :
    Measurable[𝓕.predictable] (fun p : ι × Ω => preJumpGain jumps τ Δ H p.1 p.2) := by
  classical
  let Z : ℕ → Ω → ℝ := fun k ω =>
    if k ∈ jumps ω then inner ℝ (H (τ k ω, ω)) (Δ k ω) else 0
  have hm := predictable_pre_jump_sum 𝓕 τ hτ Z hmark
  have he : (fun p : ι × Ω => ∑' k, if τ k p.2 < p.1 then Z k p.2 else 0) =
      (fun p : ι × Ω => preJumpGain jumps τ Δ H p.1 p.2) := by
    funext p
    rw [tsum_eq_sum (s := jumps p.2) (fun k hk => by simp [Z, hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Z, hk]
  rwa [he] at hm

#print axioms predictable_pre_jump_sum
#print axioms predictable_pre_jump_gain
#print axioms predictable_stopped_mark
end FTDAP
