/-
The isometry argument follows Mathlib.Analysis.Normed.Module.DoubleDual,
Copyright (c) 2020 Heather Macbeth. Apache 2.0; authors Heather Macbeth,
Michał Świętek. Here only the real normed-space case is needed.
-/
import PinnedWeakDual
import Mathlib.Analysis.Normed.Module.HahnBanach

import Mathlib.Analysis.Normed.Operator.NormedSpace
open NormedSpace Set Filter
open scoped Topology
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real Banach-space embedding into its normed bidual is isometric. -/
noncomputable def realBidualEmbedding : E →ₗᵢ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
  { (ContinuousLinearMap.apply ℝ ℝ : E →L[ℝ] StrongDual ℝ (StrongDual ℝ E)).toLinearMap with
    norm_map' x := by
      apply le_antisymm
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
        intro f
        change ‖f x‖ ≤ ‖x‖ * ‖f‖
        simpa only [mul_comm] using f.le_opNorm x
      · obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℝ x
        have h := (ContinuousLinearMap.apply ℝ ℝ x).unit_le_opNorm g hg
        change ‖x‖ ≤ ‖(ContinuousLinearMap.apply ℝ ℝ) x‖
        simpa [hgx] using h }

/-- Completeness makes the represented functionals norm closed in the bidual. -/
theorem real_bidual_range_closed [CompleteSpace E] :
    IsClosed (Set.range (realBidualEmbedding : E → StrongDual ℝ (StrongDual ℝ E))) := by
  exact (realBidualEmbedding (E := E)).isometry.isUniformInducing.isComplete_range.isClosed

/-- A norm limit of predual evaluations is still evaluation at a predual point. -/
theorem norm_limit_evaluations [CompleteSpace E] (x : ℕ → E)
    (L : StrongDual ℝ (StrongDual ℝ E))
    (hlim : Tendsto (fun n => realBidualEmbedding (x n)) atTop (𝓝 L)) :
    ∃ y : E, ∀ f : StrongDual ℝ E, L f = f y := by
  have hmem := (real_bidual_range_closed (E := E)).mem_of_tendsto hlim
    (Eventually.of_forall (fun n => Set.mem_range_self (x n)))
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  intro f
  rw [← hy]
  rfl

#print axioms real_bidual_range_closed
#print axioms norm_limit_evaluations
end FTDAP
