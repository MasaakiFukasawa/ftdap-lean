import RealBidual
import Mathlib.Analysis.Normed.Group.Bounded

open NormedSpace Set Filter Bornology
open scoped Topology
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak-star closed bounded slices already imply norm closedness. This is the
initial reduction in the Krein--Smulian argument. -/
theorem weakdual_slices_norm_closed (K : Set (WeakDual ℝ E))
    (hslice : ∀ r : ℝ, IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r})) :
    IsClosed (StrongDual.toWeakDual ⁻¹' K) := by
  apply IsSeqClosed.isClosed
  intro u x hu hlim
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto u hlim).exists_norm_le
  have hmap : Tendsto (fun n => StrongDual.toWeakDual (u n)) atTop
      (𝓝 (StrongDual.toWeakDual x)) := NormedSpace.Dual.toWeakDual_continuous.continuousAt.tendsto.comp hlim
  have hmem : StrongDual.toWeakDual x ∈ K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ R} :=
    (hslice R).mem_of_tendsto hmap (Eventually.of_forall (fun n => ⟨hu n, hR _ (mem_range_self n)⟩))
  exact hmem.1

/-- A weak-star closed norm-bounded slice is weak-star compact by Alaoglu. -/
theorem weakdual_slice_compact (K : Set (WeakDual ℝ E)) (r : ℝ)
    (hclosed : IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r})) :
    IsCompact (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}) := by
  have hb := WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := E) 0 r
  apply hb.of_isClosed_subset hclosed
  intro f hf
  change dist (WeakDual.toStrongDual f) 0 ≤ r
  simpa only [dist_zero_right, mem_ofPred_eq] using hf.2

#print axioms weakdual_slices_norm_closed
#print axioms weakdual_slice_compact
end FTDAP
