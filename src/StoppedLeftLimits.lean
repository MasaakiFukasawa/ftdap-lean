import StoppedCadlag

open MeasureTheory Set Filter Function
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The price just before a stopping time is measurable at that stopping time. -/
theorem stopped_left_limit_measurable (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (hprog : IsStronglyProgressive 𝓕 S)
    (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (σ : Ω → ℝ) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ))) :
    Measurable[hσ.measurableSpace] (fun ω => leftLim (fun t => S t ω) (σ ω)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hlimε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hm : ∀ n, Measurable[hσ.measurableSpace] (fun ω => S (σ ω - ε n) ω) := by
    intro n
    have hd : IsStronglyProgressive 𝓕 (fun t (_ : Ω) => t - ε n) := by
      apply StronglyAdapted.isStronglyProgressive_of_continuous
      · intro t
        exact stronglyMeasurable_const
      · intro ω
        exact continuous_id.sub continuous_const
    have hp := hprog.comp hd (fun t ω => sub_le_self t (hε n).le)
    exact measurable_stoppedValue hp hσ
  have hstrong : StronglyMeasurable[hσ.measurableSpace]
      (fun ω => leftLim (fun t => S t ω) (σ ω)) := by
    apply @stronglyMeasurable_of_tendsto Ω V ℕ hσ.measurableSpace _ _ atTop _ _ _ _
      (fun n => (hm n).stronglyMeasurable)
    rw [tendsto_pi_nhds]
    intro ω
    have ht : Tendsto (fun n => σ ω - ε n) atTop (𝓝 (σ ω)) := by
      simpa using (tendsto_const_nhds (x := σ ω)).sub hlimε
    have hw : Tendsto (fun n => σ ω - ε n) atTop (𝓝[<] (σ ω)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall (fun n => sub_lt_self _ (hε n))⟩
    exact (tendsto_leftLim_of_tendsto ((hcad ω).tendsto_nhdsLT (σ ω))).comp hw
  exact hstrong.measurable

/-- Actual jump increments and their nonzero events are measurable at a stopping time. -/
theorem stopped_increment_measurable (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (σ : Ω → ℝ) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ))) :
    Measurable[hσ.measurableSpace]
      (fun ω => S (σ ω) ω - leftLim (fun t => S t ω) (σ ω)) ∧
    MeasurableSet[hσ.measurableSpace]
      {ω | S (σ ω) ω - leftLim (fun t => S t ω) (σ ω) ≠ 0} := by
  have hp := adapted_right_continuous_progressive 𝓕 S hadapt
    (fun ω => (hcad ω).isRightContinuous)
  have hs : Measurable[hσ.measurableSpace] (fun ω => S (σ ω) ω) :=
    measurable_stoppedValue hp hσ
  have hd := hs.sub (stopped_left_limit_measurable 𝓕 S hp hcad σ hσ)
  exact ⟨hd, (hd (measurableSet_singleton 0)).compl⟩

#print axioms stopped_left_limit_measurable
#print axioms stopped_increment_measurable
end FTDAP
