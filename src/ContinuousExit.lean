import ContinuousHitting
import StoppedPortfolioMarks

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V]

omit [BorelSpace V] in
/-- A vector mark measurable at sigma can be tested at later deterministic times. -/
theorem stopped_vector_mark_measurable (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (σ : Ω → ℝ) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (Z : Ω → V) (hZ : Measurable[hσ.measurableSpace] Z) (t : ℝ) :
    Measurable[𝓕 t] (fun ω => if σ ω ≤ t then Z ω else 0) := by
  classical
  intro A hA
  have hmark : MeasurableSet[𝓕 t] ((Z ⁻¹' A) ∩ {ω | σ ω ≤ t}) := by
    simpa using ((hσ.measurableSet (Z ⁻¹' A)).mp (hZ hA)).2 t
  have he : (fun ω => if σ ω ≤ t then Z ω else 0) ⁻¹' A =
      ((Z ⁻¹' A) ∩ {ω | σ ω ≤ t}) ∪
        (if (0 : V) ∈ A then {ω | σ ω ≤ t}ᶜ else ∅) := by
    ext ω
    by_cases ht : σ ω ≤ t <;> by_cases hz : (0 : V) ∈ A <;> simp [ht, hz]
  rw [he]
  apply hmark.union
  split_ifs
  · exact (show MeasurableSet[𝓕 t] {ω | σ ω ≤ t} from by simpa using hσ t).compl
  · exact @MeasurableSet.empty Ω (𝓕 t)

/-- The first departure from a stopping-time measurable state is a stopping time.
The defining process need only be adapted after the starting time. -/
theorem next_state_exit_stopping_time [SecondCountableTopology V] (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    [𝓕.IsRightContinuous] (S : ℝ → Ω → V)
    (hadapt : ∀ s, Measurable[𝓕 s] (S s))
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω))
    (σ : Ω → ℝ) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ)))
    (Z : Ω → V) (hZ : Measurable[hσ.measurableSpace] Z) :
    IsStoppingTime 𝓕 (fun ω =>
      hittingAfter (fun s ω' => S s ω' - Z ω') ({0}ᶜ : Set V) (σ ω) ω) := by
  classical
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  obtain ⟨D, hD, hdense⟩ := exists_countable_dense ℝ
  have he : {ω | hittingAfter (fun s ω' => S s ω' - Z ω') ({0}ᶜ : Set V) (σ ω) ω < t} =
      ⋃ q ∈ D, (if q < t then {ω | σ ω ≤ q ∧ S q ω ≠ Z ω} else ∅) := by
    ext ω
    simp only [mem_ofPred_eq, hittingAfter_lt_iff, mem_iUnion]
    constructor
    · rintro ⟨s, hs, hchange⟩
      have hA : IsOpen ({Z ω}ᶜ : Set V) := isClosed_singleton.isOpen_compl
      have hsA : S s ω ∈ ({Z ω}ᶜ : Set V) := by simpa only [mem_compl_iff, mem_singleton_iff, sub_eq_zero] using hchange
      have he : {u | S u ω ∈ ({Z ω}ᶜ : Set V)} ∈ 𝓝[>] s :=
        (hright ω s) (hA.mem_nhds hsA)
      obtain ⟨u, hsu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hs.2).mp he
      obtain ⟨q, hqD, hsq, hqu⟩ := hdense.exists_between (lt_min hsu hs.2)
      have hqt : q < t := hqu.trans_le (min_le_right u t)
      refine ⟨q, hqD, ?_⟩
      rw [ite_eq_left hqt]
      refine ⟨hs.1.trans hsq.le, ?_⟩
      simpa using hu ⟨hsq, hqu.trans_le (min_le_left u t)⟩
    · rintro ⟨q, _, hq⟩
      by_cases hqt : q < t
      · rw [ite_eq_left hqt] at hq
        exact ⟨q, ⟨hq.1, hqt⟩, by simpa only [mem_compl_iff, mem_singleton_iff, sub_eq_zero] using hq.2⟩
      · rw [ite_eq_right hqt] at hq
        exact (notMem_empty ω hq).elim
  rw [he]
  apply MeasurableSet.biUnion hD
  intro q _
  split_ifs with hqt
  · have hloc := stopped_vector_mark_measurable 𝓕 σ hσ Z hZ q
    have hneq : MeasurableSet[𝓕 q]
        {ω | S q ω ≠ (if σ ω ≤ q then Z ω else 0)} :=
      (measurableSet_eq_fun (hadapt q) hloc).compl
    have hle : MeasurableSet[𝓕 q] {ω | σ ω ≤ q} := by simpa using hσ q
    apply 𝓕.mono hqt.le
    convert hle.inter hneq using 1
    ext ω
    by_cases h : σ ω ≤ q <;> simp [h]
  · exact @MeasurableSet.empty Ω (𝓕 t)

/-- In particular, the next change from the actual stopped price is a stopping time. -/
theorem next_price_change_stopping_time [SecondCountableTopology V]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → V) (hprog : IsStronglyProgressive 𝓕 S)
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω))
    (σ : Ω → ℝ) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ))) :
    IsStoppingTime 𝓕 (fun ω => hittingAfter
      (fun s ω' => S s ω' - S (σ ω') ω') ({0}ᶜ : Set V) (σ ω) ω) := by
  have hZ : Measurable[hσ.measurableSpace] (fun ω => S (σ ω) ω) := by
    exact measurable_stoppedValue hprog hσ
  exact next_state_exit_stopping_time 𝓕 S (fun s => (hprog.stronglyAdapted s).measurable)
    hright σ hσ (fun ω => S (σ ω) ω) hZ

#print axioms next_price_change_stopping_time
#print axioms stopped_vector_mark_measurable
#print axioms next_state_exit_stopping_time
end FTDAP
