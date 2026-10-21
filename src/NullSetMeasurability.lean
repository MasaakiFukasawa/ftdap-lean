import ContinuousStoppedMartingale

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]

/-- If a smaller sigma-algebra contains every ambient null set, changing a
measurable function on a null set preserves its measurability there. -/
theorem measurable_of_ae_eq_null_sets
    {P : Measure Ω} {m : MeasurableSpace Ω}
    (hcomplete : ∀ N : Set Ω, P N = 0 → MeasurableSet[m] N)
    {f g : Ω → W} (hg : Measurable[m] g) (he : f =ᵐ[P] g) : Measurable[m] f := by
  have hN : P {ω | f ω ≠ g ω} = 0 := ae_iff.mp he
  let : MeasurableSpace Ω := m
  intro A hA
  have hNA : P {ω | f ω ∈ A ∧ f ω ≠ g ω} = 0 :=
    measure_mono_null (fun _ h => h.2) hN
  have hpre : MeasurableSet[m] (g ⁻¹' A) := hg hA
  have hdiff := @MeasurableSet.diff Ω m (g ⁻¹' A) {ω | f ω ≠ g ω} hpre (hcomplete _ hN)
  have hm := @MeasurableSet.union Ω m _ _ hdiff (hcomplete _ hNA)
  convert hm using 1
  ext ω
  by_cases heq : f ω = g ω <;> simp [heq]

#print axioms measurable_of_ae_eq_null_sets
end FTDAP
