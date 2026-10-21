import BoundedVariationNA

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- Stop the source jump model by retaining its jumps through the stopping time. -/
noncomputable def PriceJumpModel.stop
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (σ : Ω → NNReal) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal))) :
    PriceJumpModel P 𝓕 (fun t ω => S (min t (σ ω)) ω) T := by
  classical
  let J : Ω → Finset ℕ := fun ω => (M.active ω).filter (fun k => M.times k ω ≤ σ ω)
  refine {
    active := J
    times := M.times
    marks := M.marks
    stopping := M.stopping
    measurable_marks := M.measurable_marks
    measurable_active := ?_
    injective_times := fun ω => (M.injective_times ω).mono (Finset.filter_subset _ _)
    bounds := fun ω k hk => M.bounds ω k (Finset.mem_filter.mp hk).1
    representation := ?_ }
  · intro k
    have hm := (M.stopping k).measurableSet_le_stopping_time hσ
    have hle : MeasurableSet[(M.stopping k).measurableSpace] {ω | M.times k ω ≤ σ ω} := by
      simpa only [WithTop.coe_le_coe] using hm
    simpa only [J, Finset.mem_filter, ofPred_and] using (M.measurable_active k).inter hle
  · filter_upwards [M.representation] with ω hω
    intro t ht
    have h := hω (min t (σ ω)) ((min_le_left _ _).trans ht)
    change S (min t (σ ω)) ω - S (min 0 (σ ω)) ω = _
    rw [min_eq_left (show (0 : NNReal) ≤ σ ω from bot_le), h]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hs : M.times k ω ≤ σ ω <;> by_cases hkt : M.times k ω ≤ t <;>
      simp [hs, hkt]

variable [InnerProductSpace ℝ V]

/-- Stopping the jump model stops the original gain, including the stopping jump. -/
theorem PriceJumpModel.stopped_model_gain
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (σ : Ω → NNReal) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (H : NNReal × Ω → V) (t : NNReal) (ω : Ω) :
    finiteJumpGain (M.stop σ hσ).active (M.stop σ hσ).times (M.stop σ hσ).marks H t ω =
      finiteJumpGain M.active M.times M.marks H (min t (σ ω)) ω := by
  classical
  change (∑ k ∈ (M.active ω).filter (fun k => M.times k ω ≤ σ ω),
    if M.times k ω ≤ t then inner ℝ (H (M.times k ω, ω)) (M.marks k ω) else 0) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hs : M.times k ω ≤ σ ω <;> by_cases ht : M.times k ω ≤ t <;>
    simp [hs, ht]

#print axioms PriceJumpModel.stopped_model_gain
end FTDAP
