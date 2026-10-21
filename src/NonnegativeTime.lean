import OrderedActiveJumps

open MeasureTheory Set
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Restrict a real-indexed filtration to nonnegative times. -/
def nonnegativeFiltration (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) :
    Filtration NNReal ‹MeasurableSpace Ω› where
  seq t := 𝓕 (t : ℝ)
  mono' := fun _ _ h => 𝓕.mono h
  le' t := 𝓕.le (t : ℝ)

/-- A finite real stopping time, truncated at zero, remains a stopping time
after restriction to nonnegative time. -/
theorem nonnegative_stopping_time (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (τ : Ω → ℝ) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    :
    IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (WithTop.some (Real.toNNReal (τ ω)))) := by
  intro t
  have he : {ω | WithTop.some (Real.toNNReal (τ ω)) ≤ (t : WithTop NNReal)} =
      {ω | τ ω ≤ (t : ℝ)} := by
    ext ω
    exact by simp only [mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
  change MeasurableSet[𝓕 (t : ℝ)] _
  rw [he]
  simpa only [WithTop.coe_le_coe] using hτ (t : ℝ)

/-- Restricting to nonnegative times loses no eventual information, since this
set of times is cofinal in the real line. -/
theorem nonnegative_filtration_sup (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) :
    (⨆ t : ℝ, 𝓕 t) = ⨆ t : NNReal, nonnegativeFiltration 𝓕 t := by
  apply le_antisymm
  · apply iSup_le
    intro t
    exact le_iSup_of_le (⟨max t 0, le_max_right _ _⟩ : NNReal)
      (𝓕.mono (le_max_left _ _))
  · exact iSup_le (fun t => le_iSup (fun s : ℝ => 𝓕 s) (t : ℝ))

/-- Stopped-time information, and hence measurable jump marks, transports to
nonnegative time without adding any measurability assumption. -/
theorem nonnegative_stopped_information (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (τ : Ω → ℝ) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ)))
    :
    hτ.measurableSpace ≤ (nonnegative_stopping_time 𝓕 τ hτ).measurableSpace := by
  intro A hA
  refine ⟨?_, ?_⟩
  · rw [← nonnegative_filtration_sup 𝓕]
    exact hA.1
  · intro t
    have he : {ω | WithTop.some (Real.toNNReal (τ ω)) ≤ (t : WithTop NNReal)} =
        {ω | τ ω ≤ (t : ℝ)} := by
      ext ω
      exact by simp only [mem_ofPred_eq, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
    change MeasurableSet[𝓕 (t : ℝ)] (A ∩ _)
    rw [he]
    simpa only [WithTop.coe_le_coe] using hA.2 (t : ℝ)

#print axioms nonnegative_stopping_time
#print axioms nonnegative_filtration_sup
#print axioms nonnegative_stopped_information
end FTDAP
