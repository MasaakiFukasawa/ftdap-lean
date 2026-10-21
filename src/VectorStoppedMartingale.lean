import StoppedPathContinuity

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Taking a fixed real coordinate preserves a Banach-valued martingale. -/
theorem martingale_inner_coordinate
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} (hm : Martingale S 𝓕 P) (v : V) :
    Martingale (fun t ω => inner ℝ v (S t ω)) 𝓕 P := by
  apply martingale_of_rectangle_tests P 𝓕 _
    (fun t => (continuous_const.inner continuous_id).comp_stronglyMeasurable (hm.stronglyAdapted t))
    (fun t => (hm.integrable t).const_inner v)
  intro s t hst A hA
  have hi : Integrable (fun ω => S t ω - S s ω) (P.restrict A) :=
    ((hm.integrable t).sub (hm.integrable s)).integrableOn
  have he : (∫ ω in A, S t ω - S s ω ∂P) = 0 := by
    rw [integral_sub (hm.integrable t).integrableOn (hm.integrable s).integrableOn,
      ← hm.setIntegral_eq hst hA, sub_self]
  simp_rw [← inner_sub_right]
  rw [integral_inner hi v, he, inner_zero_right]

/-- A bounded stopped vector process is a martingale, using scalar optional
sampling for every coordinate. -/
theorem bounded_vector_stopped_martingale
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} (hm : Martingale S 𝓕 P)
    (hr : ∀ ω, IsRightContinuous (fun t => S t ω))
    (σ : Ω → NNReal) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (ha : StronglyAdapted 𝓕 (fun t ω => S (min t (σ ω)) ω)) (T : NNReal)
    (b : ℝ) (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖S (min t (σ ω)) ω‖ ≤ b) :
    Martingale (fun (t : Iic T) ω => S (min t.val (σ ω)) ω) (horizonFiltration 𝓕 T) P := by
  have hint : ∀ t : Iic T, Integrable (fun ω => S (min t.val (σ ω)) ω) P := by
    intro t
    have hmeas := (ha t.val).mono (𝓕.le t.val)
    exact (show MemLp _ 1 P from MemLp.of_bound hmeas.aestronglyMeasurable b
      (hbound.mono (fun _ h => h t.val t.property))).integrable le_rfl
  have hcoord : ∀ v : V, Martingale
      (fun (t : Iic T) ω => inner ℝ v (S (min t.val (σ ω)) ω)) (horizonFiltration 𝓕 T) P := by
    intro v
    apply continuous_stopped_martingale (martingale_inner_coordinate hm v)
      (fun ω => (hr ω).continuous_comp (continuous_const.inner continuous_id)) σ hσ
      (fun t => (continuous_const.inner continuous_id).comp_stronglyMeasurable (ha t)) T
  apply martingale_of_rectangle_tests P (horizonFiltration 𝓕 T) _ (fun t => ha t.val) hint
  intro s t hst A hA
  have hi : Integrable (fun ω => S (min t.val (σ ω)) ω - S (min s.val (σ ω)) ω)
      (P.restrict A) := ((hint t).sub (hint s)).integrableOn
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hi
  intro v
  simp_rw [inner_sub_right]
  rw [integral_sub ((hcoord v).integrable t).integrableOn ((hcoord v).integrable s).integrableOn,
    ← (hcoord v).setIntegral_eq hst hA, sub_self]

#print axioms martingale_inner_coordinate
#print axioms bounded_vector_stopped_martingale
end FTDAP
