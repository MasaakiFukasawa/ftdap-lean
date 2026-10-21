import RealBidual
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open NormedSpace Set Filter
open scoped Topology BoundedContinuousFunction
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation on a uniformly bounded sequence, as a bounded sequence. -/
noncomputable def sequenceEvaluation (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1) :
    StrongDual ℝ E →L[ℝ] (ℕ →ᵇ ℝ) := by
  let T : StrongDual ℝ E →ₗ[ℝ] (ℕ →ᵇ ℝ) := {
    toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup (fun n => f (x n))
      continuous_of_discreteTopology ‖f‖ (fun n =>
        (f.le_opNorm _).trans (by nlinarith [hx n, norm_nonneg f]))
    map_add' := by
      intro f g
      ext n
      rfl
    map_smul' := by
      intro r f
      ext n
      rfl }
  exact T.mkContinuous 1 (fun f => by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro n
    exact (f.le_opNorm _).trans (by nlinarith [hx n, norm_nonneg f]))

@[simp]
theorem sequenceEvaluation_apply (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (f : StrongDual ℝ E) (n : ℕ) : sequenceEvaluation x hx f n = f (x n) := rfl

omit [NormedSpace ℝ E] in
/-- Finite truncations of a unit-bounded sequence remain unit bounded. -/
theorem truncated_sequence_bound (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1) (N n : ℕ) :
    ‖if n < N then x n else 0‖ ≤ 1 := by
  split_ifs
  · exact hx n
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation operators of a null sequence are norm limits of their
finite-rank truncations. -/
theorem sequenceEvaluation_truncations_tendsto (x : ℕ → E) (hx : ∀ n, ‖x n‖ ≤ 1)
    (hlim : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun N => sequenceEvaluation (fun n => if n < N then x n else 0)
      (truncated_sequence_bound x hx N)) atTop (𝓝 (sequenceEvaluation x hx)) := by
  apply (Metric.tendsto_atTop (α := StrongDual ℝ E →L[ℝ] (ℕ →ᵇ ℝ))).mpr
  intro ε hε
  have he : ∀ᶠ n in atTop, ‖x n‖ < ε / 2 := by
    apply eventually_atTop.mpr
    simpa only [dist_zero_right] using (Metric.tendsto_atTop.mp hlim) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro M hNM
  rw [@dist_eq_norm (StrongDual ℝ E →L[ℝ] (ℕ →ᵇ ℝ))
    ContinuousLinearMap.toSeminormedAddCommGroup]
  have hb : ‖sequenceEvaluation (fun n => if n < M then x n else 0)
      (truncated_sequence_bound x hx M) - sequenceEvaluation x hx‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity : 0 ≤ ε / 2)
    intro f
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (by positivity : 0 ≤ ε / 2) (norm_nonneg f))).mpr
    intro n
    by_cases hn : n < M
    · simp only [sub_apply, BoundedContinuousFunction.sub_apply,
        sequenceEvaluation_apply, ite_eq_left hn, sub_self, norm_zero]
      positivity
    · have hxn := (hN n (hNM.trans (Nat.le_of_not_gt hn))).le
      simp only [sub_apply, BoundedContinuousFunction.sub_apply,
        sequenceEvaluation_apply, ite_eq_right hn, map_zero, zero_sub, norm_neg]
      exact (f.le_opNorm _).trans (by nlinarith [hxn, norm_nonneg f])
  exact lt_of_le_of_lt hb (by linarith)

#print axioms truncated_sequence_bound
#print axioms sequenceEvaluation_truncations_tendsto
end FTDAP
