import NullSequenceEvaluation

open NormedSpace Set Filter
open scoped Topology BoundedContinuousFunction
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single coordinate vector in the bounded-sequence space. -/
noncomputable def sequenceCoordinate (k : ℕ) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun n => if n = k then 1 else 0)
    continuous_of_discreteTopology 1 (fun n => by split_ifs <;> norm_num)

/-- A truncated evaluation sequence is a finite linear combination of coordinate vectors. -/
theorem truncated_evaluation_expansion (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (N : ℕ) (f : StrongDual ℝ E) :
    sequenceEvaluation (fun n => if n < N then x n else 0) (truncated_sequence_bound x hx N) f =
      ∑ k ∈ Finset.range N, (f (x k)) • sequenceCoordinate k := by
  ext n
  simp only [sequenceEvaluation_apply, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, sequenceCoordinate,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, smul_eq_mul]
  by_cases hn : n < N
  · rw [ite_eq_left hn]
    symm
    rw [Finset.sum_eq_single n]
    · simp
    · intro k _ hkn
      simp [Ne.symm hkn]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hn)).elim
  · rw [ite_eq_right hn, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hnk : n ≠ k := fun h => hn (h ▸ Finset.mem_range.mp hk)
    simp [hnk]

/-- Composing a finite evaluation operator with any continuous functional is
represented by an explicit finite predual vector. -/
theorem truncated_evaluation_adjoint (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (ρ : StrongDual ℝ (ℕ →ᵇ ℝ)) (N : ℕ) :
    ρ.comp (sequenceEvaluation (fun n => if n < N then x n else 0) (truncated_sequence_bound x hx N)) =
      realBidualEmbedding (∑ k ∈ Finset.range N, (ρ (sequenceCoordinate k)) • x k) := by
  ext f
  change ρ (sequenceEvaluation (fun n => if n < N then x n else 0)
    (truncated_sequence_bound x hx N) f) = f (∑ k ∈ Finset.range N, (ρ (sequenceCoordinate k)) • x k)
  rw [truncated_evaluation_expansion x hx N f]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- For a Banach predual, composing a null-sequence evaluation operator with
any norm-continuous functional is weak-star evaluation at a predual point.
This avoids needing a separate duality theorem for the sequence space. -/
theorem null_sequence_functional_is_evaluation [CompleteSpace E]
    (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1) (hlim : Tendsto x atTop (𝓝 0))
    (ρ : StrongDual ℝ (ℕ →ᵇ ℝ)) :
    ∃ y : E, ∀ f : StrongDual ℝ E, ρ (sequenceEvaluation x hx f) = f y := by
  have hcomp := (((ContinuousLinearMap.compL ℝ (StrongDual ℝ E) (ℕ →ᵇ ℝ) ℝ) ρ).continuous.tendsto
    (sequenceEvaluation x hx)).comp (sequenceEvaluation_truncations_tendsto x hx hlim)
  have he : (fun N => ρ.comp (sequenceEvaluation (fun n => if n < N then x n else 0)
      (truncated_sequence_bound x hx N))) =
      fun N => realBidualEmbedding (∑ k ∈ Finset.range N, (ρ (sequenceCoordinate k)) • x k) :=
    funext (fun N => truncated_evaluation_adjoint x hx ρ N)
  change Tendsto (fun N => ρ.comp (sequenceEvaluation (fun n => if n < N then x n else 0)
    (truncated_sequence_bound x hx N))) atTop (𝓝 (ρ.comp (sequenceEvaluation x hx))) at hcomp
  rw [he] at hcomp
  exact norm_limit_evaluations _ _ hcomp

#print axioms truncated_evaluation_expansion
#print axioms truncated_evaluation_adjoint
#print axioms null_sequence_functional_is_evaluation
end FTDAP
