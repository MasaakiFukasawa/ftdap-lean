import ContinuousExit
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP

noncomputable def upperGrid (n : ℕ) (t : ℝ) : ℝ :=
  ((⌊t * ((n : ℝ)+1)⌋ : ℝ) + 1) / ((n : ℝ)+1)

theorem upper_grid_bounds (n : ℕ) (t : ℝ) :
    t < upperGrid n t ∧ upperGrid n t ≤ t + 1 / ((n : ℝ)+1) := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  constructor
  · apply (lt_div_iff₀ hn).mpr
    exact Int.lt_floor_add_one _
  · apply (div_le_iff₀ hn).mpr
    have hf := Int.floor_le (t * ((n : ℝ)+1))
    have hi : (1 / ((n : ℝ)+1)) * ((n : ℝ)+1) = 1 := div_mul_cancel₀ 1 hn.ne'
    nlinarith

theorem upper_grid_tendsto (t : ℝ) : Tendsto (fun n => upperGrid n t) atTop (𝓝 t) := by
  have he : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ)+1)) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
    (fun n => (upper_grid_bounds n t).1.le) (fun n => (upper_grid_bounds n t).2)

variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Adapted right-continuous real-time processes are progressively measurable.
The upper time grid is capped at the deterministic section endpoint. -/
theorem adapted_right_continuous_progressive (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hright : ∀ ω, IsRightContinuous (fun t => S t ω)) :
    IsStronglyProgressive 𝓕 S := by
  intro T
  let m : MeasurableSpace (Iic T × Ω) := MeasurableSpace.prod inferInstance (𝓕 T)
  let A : ℕ → Iic T × Ω → V := fun n p => S (min (upperGrid n p.1) T) p.2
  have hm : ∀ n, @Measurable _ V m _ (A n) := by
    intro n
    have hsections : ∀ z : ℤ, Measurable[𝓕 T]
        (S (min (((z : ℝ)+1) / ((n : ℝ)+1)) T)) := fun z =>
      (hadapt _).mono (𝓕.mono (min_le_right _ _)) le_rfl
    have htable := measurable_from_prod_countable_right
      (f := fun q : ℤ × Ω => S (min (((q.1 : ℝ)+1) / ((n : ℝ)+1)) T) q.2) hsections
    have hgrid : Measurable (fun t : Iic T => ⌊(t : ℝ) * ((n : ℝ)+1)⌋) :=
      (measurable_subtype_coe.mul_const _).floor
    exact htable.comp ((hgrid.comp measurable_fst).prodMk measurable_snd)
  apply @stronglyMeasurable_of_tendsto _ V ℕ m _ _ atTop _ _ _ _
    (fun n => (hm n).stronglyMeasurable)
  rw [tendsto_pi_nhds]
  intro p
  have hpt : (p.1 : ℝ) ≤ T := p.1.2
  rcases hpt.eq_or_lt with he | ht
  · have heq : ∀ n, min (upperGrid n p.1) T = T := fun n =>
      min_eq_right (he.symm.le.trans (upper_grid_bounds n p.1).1.le)
    change Tendsto (fun n => S (min (upperGrid n p.1) T) p.2) atTop (𝓝 (S p.1 p.2))
    simp_rw [heq, he]
    exact tendsto_const_nhds
  · have hgridlim : Tendsto (fun n => min (upperGrid n p.1) T) atTop (𝓝 (p.1 : ℝ)) := by
      simpa only [min_eq_left hpt] using Tendsto.min (upper_grid_tendsto p.1) (tendsto_const_nhds (x := T))
    have hwithin : Tendsto (fun n => min (upperGrid n p.1) T) atTop (𝓝[>] (p.1 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hgridlim,
        Eventually.of_forall (fun n => lt_min (upper_grid_bounds n p.1).1 ht)⟩
    exact (hright p.2 p.1).tendsto.comp hwithin

#print axioms upper_grid_bounds
#print axioms upper_grid_tendsto
#print axioms adapted_right_continuous_progressive
end FTDAP
