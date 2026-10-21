import TradingCone

open MeasureTheory Set
open scoped RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {α V β : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [InnerProductSpace ℝ V] in
/-- A finite table can be selected measurably from measurable fibers. -/
theorem measurable_finite_selection (S : Finset β) (J : α → β)
    (hJ : ∀ a, J a ∈ S) (hfiber : ∀ b ∈ S, MeasurableSet {a | J a = b})
    (u : β → V) : Measurable (fun a => u (J a)) := by
  have he : (fun a => u (J a)) = fun a => ∑ b ∈ S, if J a = b then u b else 0 := by
    funext a
    symm
    rw [Finset.sum_eq_single (J a)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hn
      exact (hn (hJ a)).elim
  rw [he]
  apply Finset.measurable_sum
  intro b hb
  exact measurable_const.piecewise (hfiber b hb) measurable_const

/-- A finite table of continuous linear projections can likewise be selected. -/
theorem measurable_finite_projection (S : Finset β) (J : α → β)
    (hJ : ∀ a, J a ∈ S) (hfiber : ∀ b ∈ S, MeasurableSet {a | J a = b})
    (P : β → V →L[ℝ] V) (H : α → V) (hH : Measurable H) :
    Measurable (fun a => P (J a) (H a)) := by
  have he : (fun a => P (J a) (H a)) =
      fun a => ∑ b ∈ S, if J a = b then P b (H a) else 0 := by
    funext a
    symm
    rw [Finset.sum_eq_single (J a)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hn
      exact (hn (hJ a)).elim
  rw [he]
  apply Finset.measurable_sum
  intro b hb
  exact ((P b).continuous.measurable.comp hH).piecewise (hfiber b hb) measurable_const

noncomputable def constraintSet (F : Finset V) (H : α → V) (W : α → ℝ) (a : α) : Finset V :=
  F.filter (fun z => -W a ≤ ⟪H a, z⟫)

omit [SecondCountableTopology V] in
theorem constraint_set_fiber_measurable (F : Finset V) (H : α → V) (W : α → ℝ)
    (hH : Measurable H) (hW : Measurable W) (J : Finset V) (hJF : J ⊆ F) :
    MeasurableSet {a | constraintSet F H W a = J} := by
  have hz : ∀ z ∈ F, MeasurableSet {a | z ∈ constraintSet F H W a ↔ z ∈ J} := by
    intro z hzF
    have hm : MeasurableSet {a | -W a ≤ ⟪H a, z⟫} :=
      measurableSet_le hW.neg ((continuous_id.inner continuous_const).measurable.comp hH)
    by_cases hzJ : z ∈ J
    · simpa [constraintSet, hzF, hzJ] using hm
    · simpa only [constraintSet, Finset.mem_filter, hzF, true_and, hzJ, iff_false,
        compl_ofPred] using hm.compl
  have he : {a | constraintSet F H W a = J} =
      ⋂ z ∈ (F : Set V), {a | z ∈ constraintSet F H W a ↔ z ∈ J} := by
    ext a
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro he z _
      rw [he]
    · intro he
      apply Finset.ext
      intro z
      by_cases hzF : z ∈ F
      · exact he z hzF
      · have hzJ : z ∉ J := fun h => hzF (hJF h)
        simp [constraintSet, hzF, hzJ]
  rw [he]
  exact MeasurableSet.biInter F.finite_toSet.countable hz

#print axioms measurable_finite_selection
#print axioms measurable_finite_projection
#print axioms constraint_set_fiber_measurable
end FTDAP
