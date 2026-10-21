import NullSequencePredual
import Mathlib.Analysis.LocallyConvex.Separation

open NormedSpace Set Filter
open scoped Topology BoundedContinuousFunction
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A null sequence that detects every member of a convex dual set yields a
single predual separator. This is the final separation step of Krein--Smulian. -/
theorem predual_separator_of_null_sequence (K : Set (WeakDual ℝ E)) (hK : Convex ℝ K)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1) (hlim : Tendsto x atTop (𝓝 0))
    (hdetect : ∀ f ∈ K, ∃ n, 1 < f (x n)) :
    ∃ y : E, ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ K, δ ≤ f y := by
  let T := sequenceEvaluation x hx
  let L : WeakDual ℝ E →ₗ[ℝ] (ℕ →ᵇ ℝ) := T.toLinearMap.comp WeakDual.toStrongDual.toLinearMap
  let A := L '' K
  have hAconv : Convex ℝ A := hK.linear_image L
  have hAnorm : ∀ g ∈ A, 1 ≤ ‖g‖ := by
    rintro g ⟨f, hf, rfl⟩
    obtain ⟨n, hn⟩ := hdetect f hf
    have he : L f n = f (x n) := rfl
    have hb := (L f).norm_coe_le_norm n
    rw [he, Real.norm_eq_abs] at hb
    exact le_of_lt (hn.trans_le ((le_abs_self _).trans hb))
  have hclosed : IsClosed {g : ℕ →ᵇ ℝ | 1 ≤ ‖g‖} := isClosed_le continuous_const continuous_norm
  have hzero : (0 : ℕ →ᵇ ℝ) ∉ closure A := by
    intro h
    have hh := (closure_minimal hAnorm hclosed) h
    have hh0 : (1 : ℝ) ≤ ‖(0 : ℕ →ᵇ ℝ)‖ := hh
    norm_num at hh0
  obtain ⟨ρ, b, hρ, hb⟩ := geometric_hahn_banach_closed_point hAconv.closure isClosed_closure hzero
  have hb0 : b < 0 := by simpa using hb
  obtain ⟨y, hy⟩ := null_sequence_functional_is_evaluation x hx hlim (-ρ)
  refine ⟨y, -b, neg_pos.mpr hb0, ?_⟩
  intro f hf
  have h := hρ (L f) (subset_closure ⟨f, hf, rfl⟩)
  have he := hy (WeakDual.toStrongDual f)
  change -ρ (L f) = f y at he
  linarith

/-- Such a convex set misses zero even in weak-star closure. -/
theorem zero_not_weakstar_closure_of_null_sequence
    (K : Set (WeakDual ℝ E)) (hK : Convex ℝ K)
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1) (hlim : Tendsto x atTop (𝓝 0))
    (hdetect : ∀ f ∈ K, ∃ n, 1 < f (x n)) :
    (0 : WeakDual ℝ E) ∉ closure K := by
  obtain ⟨y, δ, hδ, hy⟩ := predual_separator_of_null_sequence K hK x hx hlim hdetect
  have hc : IsClosed {f : WeakDual ℝ E | δ ≤ f y} :=
    isClosed_le continuous_const (WeakDual.eval_continuous y)
  intro h
  have hh := (closure_minimal hy hc) h
  have hzero : δ ≤ (0 : WeakDual ℝ E) y := hh
  simpa using (not_le_of_gt hδ hzero)

#print axioms predual_separator_of_null_sequence
#print axioms zero_not_weakstar_closure_of_null_sequence
end FTDAP
