import EquivalentMeasure
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω ι E : Type*} [MeasurableSpace Ω] [Preorder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Vanishing predictable rectangle tests identify the genuine conditional
expectation definition of a martingale, with arbitrary ordered time and Banach values. -/
theorem martingale_of_rectangle_tests (Q : Measure Ω) [IsFiniteMeasure Q]
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (S : ι → Ω → E)
    (hadapt : StronglyAdapted 𝓕 S) (hint : ∀ t, Integrable (S t) Q)
    (htest : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
      (∫ ω in A, S t ω - S s ω ∂Q) = 0) : Martingale S 𝓕 Q := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hint t)
  · intro A _ _
    exact (hint s).integrableOn
  · intro A hA _
    have h := htest s t hst A hA
    rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at h
    exact (sub_eq_zero.mp h).symm
  · exact (hadapt s).aestronglyMeasurable

/-- Both signs of each scalar rectangle gain are enough to give the required
zero test, hence a martingale. -/
theorem martingale_of_signed_rectangle_tests (Q : Measure Ω) [IsFiniteMeasure Q]
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (S : ι → Ω → ℝ)
    (hadapt : StronglyAdapted 𝓕 S) (hint : ∀ t, Integrable (S t) Q)
    (htest : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
      (∫ ω in A, S t ω - S s ω ∂Q) ≤ 0 ∧
      (∫ ω in A, -(S t ω - S s ω) ∂Q) ≤ 0) : Martingale S 𝓕 Q := by
  apply martingale_of_rectangle_tests Q 𝓕 S hadapt hint
  intro s t hst A hA
  obtain ⟨hp, hn⟩ := htest s t hst A hA
  rw [integral_neg] at hn
  linarith

#print axioms martingale_of_rectangle_tests
#print axioms martingale_of_signed_rectangle_tests
end FTDAP
