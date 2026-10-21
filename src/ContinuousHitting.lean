import Continuation
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [TopologicalSpace V]
  [MeasurableSpace V] [OpensMeasurableSpace V]

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
/-- A right-continuous path hits an open set before t exactly when it does so
at a time in any fixed dense set before t. -/
theorem right_continuous_open_hit_dense (S : ℝ → V)
    (hS : IsRightContinuous S) (A : Set V) (hA : IsOpen A)
    (D : Set ℝ) (hD : Dense D) (t : ℝ) :
    (∃ s < t, S s ∈ A) ↔ ∃ q ∈ D, q < t ∧ S q ∈ A := by
  constructor
  · rintro ⟨s, hst, hs⟩
    have he : {u | S u ∈ A} ∈ 𝓝[>] s := (hS s) (hA.mem_nhds hs)
    obtain ⟨u, hsu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hst).mp he
    obtain ⟨q, hqD, hsq, hqu⟩ := hD.exists_between (lt_min hsu hst)
    exact ⟨q, hqD, hqu.trans_le (min_le_right u t),
      hu ⟨hsq, hqu.trans_le (min_le_left u t)⟩⟩
  · rintro ⟨q, _, hqt, hq⟩
    exact ⟨q, hqt, hq⟩

/-- Adapted right-continuous prices have measurable open-hit events before
an arbitrary real time, without a discrete-time restriction. -/
theorem measurable_open_hit_before (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (hadapt : ∀ s, Measurable[𝓕 s] (S s))
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω))
    (A : Set V) (hA : IsOpen A) (t : ℝ) :
    MeasurableSet[𝓕 t] {ω | ∃ s < t, S s ω ∈ A} := by
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense ℝ
  have he : {ω | ∃ s < t, S s ω ∈ A} =
      ⋃ q ∈ D, (if q < t then (S q ⁻¹' A) else ∅) := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [right_continuous_open_hit_dense (fun s => S s ω) (hright ω) A hA D hdense t]
    simp only [mem_iUnion, mem_ite, mem_preimage, mem_empty_iff_false]
    aesop
  rw [he]
  apply MeasurableSet.biUnion hD
  intro q _
  split_ifs with hqt
  · exact 𝓕.mono hqt.le _ (hadapt q hA.measurableSet)
  · exact @MeasurableSet.empty Ω (𝓕 t)

/-- Countable detection also respects a deterministic lower starting time. -/
theorem measurable_open_hit_between (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (hadapt : ∀ s, Measurable[𝓕 s] (S s))
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω))
    (A : Set V) (hA : IsOpen A) (n t : ℝ) :
    MeasurableSet[𝓕 t] {ω | ∃ s ∈ Ico n t, S s ω ∈ A} := by
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense ℝ
  have he : {ω | ∃ s ∈ Ico n t, S s ω ∈ A} =
      ⋃ q ∈ D, (if n ≤ q ∧ q < t then (S q ⁻¹' A) else ∅) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨s, hs, hSA⟩
      have he : {u | S u ω ∈ A} ∈ 𝓝[>] s := (hright ω s) (hA.mem_nhds hSA)
      obtain ⟨u, hsu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hs.2).mp he
      obtain ⟨q, hqD, hsq, hqu⟩ := hdense.exists_between (lt_min hsu hs.2)
      have hnq : n ≤ q := hs.1.trans hsq.le
      have hqt : q < t := hqu.trans_le (min_le_right u t)
      refine ⟨q, hqD, ?_⟩
      rw [ite_eq_left ⟨hnq, hqt⟩]
      exact hu ⟨hsq, hqu.trans_le (min_le_left u t)⟩
    · rintro ⟨q, hqD, hq⟩
      by_cases hqt : n ≤ q ∧ q < t
      · rw [ite_eq_left hqt] at hq
        exact ⟨q, hqt, hq⟩
      · rw [ite_eq_right hqt] at hq
        exact (notMem_empty ω hq).elim
  rw [he]
  apply MeasurableSet.biUnion hD
  intro q _
  split_ifs with hqt
  · exact 𝓕.mono hqt.2.le _ (hadapt q hA.measurableSet)
  · exact @MeasurableSet.empty Ω (𝓕 t)

/-- Continuous-time open hitting times are stopping times for a right-continuous
filtration and an adapted right-continuous process. -/
theorem open_hitting_after_stopping_time (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    [𝓕.IsRightContinuous] (S : ℝ → Ω → V)
    (hadapt : ∀ s, Measurable[𝓕 s] (S s))
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω))
    (A : Set V) (hA : IsOpen A) (n : ℝ) :
    IsStoppingTime 𝓕 (hittingAfter S A n) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  have he : {ω | hittingAfter S A n ω < t} =
      {ω | ∃ s ∈ Ico n t, S s ω ∈ A} := by
    ext ω
    exact hittingAfter_lt_iff
  rw [he]
  exact measurable_open_hit_between 𝓕 S hadapt hright A hA n t

#print axioms measurable_open_hit_between
#print axioms open_hitting_after_stopping_time
#print axioms right_continuous_open_hit_dense
#print axioms measurable_open_hit_before
end FTDAP
