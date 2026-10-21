import DensitySeries

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Kreps–Yan: a closed cone with no positive claim has a strictly positive
integrable separating density, for the actual weak L∞/L¹ topology. -/
theorem kreps_yan_positive_density (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set (WeakClaims P)) (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ f ∈ C, r • f ∈ C)
    (hneg : ∀ f : Lp ℝ ∞ P, 0 ≤ f → weakClaim P (-f) ∈ C)
    (hna : ∀ f ∈ C, 0 ≤ claimValue P f → f = 0) :
    ∃ Z : Lp ℝ 1 P, (∀ᵐ ω ∂P, 0 < Z ω) ∧
      ∀ f ∈ C, claimsPairing P f Z ≤ 0 := by
  classical
  let family : Set (Set Ω) := {A | ∃ z : Lp ℝ 1 P, 0 ≤ z ∧
    (∀ f ∈ C, claimsPairing P f z ≤ 0) ∧ A = {ω | 0 < z ω}}
  have hm : ∀ A ∈ family, MeasurableSet A := by
    rintro A ⟨z, _, _, rfl⟩
    exact measurableSet_lt measurable_const z.val.measurable
  obtain ⟨D, hDC, hcount, hcover⟩ := Measure.exists_ae_subset_biUnion_countable P hm
  let : Encodable D := hcount.toEncodable
  have hex : ∀ i : D, ∃ z : Lp ℝ 1 P, 0 ≤ z ∧
      (∀ f ∈ C, claimsPairing P f z ≤ 0) ∧ (i : Set Ω) = {ω | 0 < z ω} :=
    fun i => hDC i.property
  choose z hz hs heq using hex
  obtain ⟨Z, hZ, hsep, hsupport⟩ := aggregate_separating_densities P C z hz hs
  have hD : (⋃₀ D) ≤ᵐ[P] {ω | 0 < Z ω} := by
    filter_upwards [hsupport] with ω hω
    rintro ⟨A, hA, hωA⟩
    apply hω ⟨A, hA⟩
    have he := heq ⟨A, hA⟩
    change A = {ω | 0 < z ⟨A, hA⟩ ω} at he
    rwa [he] at hωA
  have hall : ∀ y : Lp ℝ 1 P, 0 ≤ y →
      (∀ f ∈ C, claimsPairing P f y ≤ 0) →
      {ω | 0 < y ω} ≤ᵐ[P] {ω | 0 < Z ω} := by
    intro y hy hysep
    exact (hcover _ ⟨y, hy, hysep, rfl⟩).trans hD
  let A : Set Ω := {ω | Z ω ≤ 0}
  have hA : MeasurableSet A := measurableSet_le Z.val.measurable measurable_const
  have hnull : P A = 0 := by
    by_contra hp
    obtain ⟨y, hy, hyA, hysep⟩ :=
      kreps_yan_event_separator P C hconv hclosed hscale hneg hna A hA hp
    have hyzero : A.indicator (fun ω => y ω) =ᵐ[P] 0 := by
      filter_upwards [hall y hy hysep, (Lp.coeFn_nonneg y).mpr hy] with ω hω hn
      by_cases hωA : ω ∈ A
      · rw [Set.indicator_of_mem hωA]
        have hnot : ¬ 0 < y ω := fun h => (not_lt_of_ge hωA) (hω h)
        exact le_antisymm (le_of_not_gt hnot) hn
      · simp [Set.indicator_of_notMem hωA]
    have hi : ∫ ω in A, y ω ∂P = 0 := by
      rw [← integral_indicator hA]
      exact (integral_congr_ae hyzero).trans (integral_zero Ω ℝ)
    linarith
  refine ⟨Z, ?_, hsep⟩
  have hnot : ∀ᵐ ω ∂P, ω ∉ A := ae_iff.mpr (by simpa using hnull)
  filter_upwards [hnot] with ω hω
  exact lt_of_not_ge hω

#print axioms kreps_yan_positive_density
end FTDAP
