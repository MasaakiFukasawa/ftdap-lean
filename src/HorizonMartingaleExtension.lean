import ContinuousOptionalSampling

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CompleteSpace V]

/-- A martingale on a closed finite horizon extends constantly after its
endpoint as a martingale for the original filtration. -/
theorem martingale_extend_horizon
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›} {S : NNReal → Ω → V}
    {T : NNReal} (hm : Martingale (fun (t : Iic T) => S t.val) (horizonFiltration 𝓕 T) P) :
    Martingale (fun t => S (min t T)) 𝓕 P := by
  have hadapt : StronglyAdapted 𝓕 (fun t => S (min t T)) := by
    intro t
    exact (hm.stronglyAdapted ⟨min t T, Set.mem_Iic.mpr (min_le_right _ _)⟩).mono (𝓕.mono (min_le_left _ _))
  have hint : ∀ t : NNReal, Integrable (S (min t T)) P :=
    fun t => hm.integrable ⟨min t T, Set.mem_Iic.mpr (min_le_right _ _)⟩
  apply martingale_of_rectangle_tests P 𝓕 _ hadapt hint
  intro s t hst A hA
  by_cases hs : s ≤ T
  · have h := hm.setIntegral_eq (i := ⟨s, hs⟩) (j := ⟨min t T, Set.mem_Iic.mpr (min_le_right _ _)⟩)
      (le_min hst hs) hA
    rw [integral_sub (hint t).integrableOn (hint s).integrableOn,
      min_eq_left hs]
    exact sub_eq_zero.mpr h.symm
  · have hsT := le_of_not_ge hs
    have htT := hsT.trans hst
    simp only [min_eq_right hsT, min_eq_right htT, sub_self, integral_zero]

#print axioms martingale_extend_horizon
end FTDAP
