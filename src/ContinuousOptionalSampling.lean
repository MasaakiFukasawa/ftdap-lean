import StoppingGrid

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Optional sampling for real martingales at bounded continuous-time stopping
times, using right-continuity and uniform integrability of terminal conditional
expectations. -/
theorem martingale_bounded_optional_sampling
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›} {S : NNReal → Ω → ℝ}
    (hm : Martingale S 𝓕 P) (hr : ∀ ω, IsRightContinuous (fun t => S t ω))
    (σ : Ω → NNReal) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (T : NNReal) (hT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω => S (σ ω) ω) P ∧
      ∀ A, MeasurableSet[hσ.measurableSpace] A →
        (∫ ω in A, S (σ ω) ω ∂P) = ∫ ω in A, S T ω ∂P := by
  let τ := fun n ω => min (ceilGrid n (σ ω)) T
  have hτ := fun n => capped_ceilGrid_stopping hσ n T
  have hle : ∀ n ω, (τ n ω : WithTop NNReal) ≤ T := by
    intro n ω
    exact_mod_cast min_le_right (ceilGrid n (σ ω)) T
  have he : ∀ n, (fun ω => S (τ n ω) ω) =ᵐ[P]
      P[S T | (hτ n).measurableSpace] := by
    intro n
    have hh := hm.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hτ n) (hle n)
      (capped_ceilGrid_countable σ n T)
    have hv : stoppedValue S (fun ω => (min (ceilGrid n (σ ω)) T : WithTop NNReal)) =
        (fun ω => S (τ n ω) ω) := by
      funext ω
      rfl
    rw [hv] at hh
    exact hh
  have hui : UniformIntegrable (fun n ω => S (τ n ω) ω) 1 P :=
    (hm.integrable T).uniformIntegrable_condExp
      (fun n => (hτ n).measurableSpace_le) |>.ae_eq (fun n => (he n).symm)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => S (τ n ω) ω) atTop (𝓝 (S (σ ω) ω)) := by
    apply Eventually.of_forall
    intro ω
    have hc : ContinuousWithinAt (fun t => S t ω) (Ici (σ ω)) (σ ω) := by
      have heq : insert (σ ω) (Ioi (σ ω)) = Ici (σ ω) := by
        ext x
        simp only [mem_insert_iff, mem_Ioi, mem_Ici]
        constructor
        · rintro (rfl | hx)
          · exact le_rfl
          · exact hx.le
        · intro hx
          rcases hx.eq_or_lt with he | hl
          · exact Or.inl he.symm
          · exact Or.inr hl
      rw [← heq]
      exact (hr ω (σ ω)).insert
    apply hc.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [min_eq_left (hT ω)] using
        (ceilGrid_tendsto (σ ω)).min (tendsto_const_nhds (x := T))
    · exact Eventually.of_forall (fun n => le_min (le_ceilGrid n (σ ω)) (hT ω))
  have hi := hui.integrable_of_ae_tendsto hlim
  have hlp := tendsto_Lp_finite_of_tendsto_ae (le_refl 1) ENNReal.one_ne_top
    (fun n => hui.aestronglyMeasurable n) (memLp_one_iff_integrable.mpr hi) hui.1 hlim
  refine ⟨hi, ?_⟩
  intro A hA
  have hconv := tendsto_setIntegral_of_L1' (fun ω => S (σ ω) ω)
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hui.memLp n))) hlp A
  have hall : ∀ n, (∫ ω in A, S (τ n ω) ω ∂P) = ∫ ω in A, S T ω ∂P := by
    intro n
    have hsub := hσ.measurableSpace_mono (hτ n) (fun ω => by
      change (σ ω : WithTop NNReal) ≤ (τ n ω : WithTop NNReal)
      exact WithTop.coe_le_coe.mpr (le_min (le_ceilGrid n (σ ω)) (hT ω)))
    calc
      (∫ ω in A, S (τ n ω) ω ∂P) = ∫ ω in A, P[S T | (hτ n).measurableSpace] ω ∂P :=
        integral_congr_ae (ae_restrict_of_ae (he n))
      _ = ∫ ω in A, S T ω ∂P :=
        setIntegral_condExp (hτ n).measurableSpace_le (hm.integrable T) (hsub A hA)
  exact tendsto_nhds_unique (hconv.congr (fun n => hall n)) tendsto_const_nhds

#print axioms martingale_bounded_optional_sampling
end FTDAP
