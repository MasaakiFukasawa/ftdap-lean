import FiniteFamilyNullSequence
import NullSequenceSeparation

open NormedSpace Set Filter
open scoped Topology
namespace FTDAP
attribute [local instance] Classical.decEq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extend a finite detector from one norm slice to the next, using only
small new vectors and weak-star compactness of the remaining slice. -/
theorem finite_detector_step (K : Set (WeakDual ℝ E))
    (hslice : ∀ r : ℝ, IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}))
    (n : ℕ) (D : Finset E)
    (hD : ∀ f ∈ K, ‖WeakDual.toStrongDual f‖ ≤ (n : ℝ)+1 → ∃ v ∈ D, 1 < f v) :
    ∃ S : Finset E, (∀ v ∈ S, ‖v‖ ≤ 1 / ((n : ℝ)+1)) ∧
      ∀ f ∈ K, ‖WeakDual.toStrongDual f‖ ≤ (n : ℝ)+2 → ∃ v ∈ D ∪ S, 1 < f v := by
  classical
  let U : Set (WeakDual ℝ E) := {f | ∀ v ∈ D, f v ≤ 1}
  have hU : IsClosed U := by
    simp only [U, ofPred_forall]
    exact isClosed_iInter (fun v => isClosed_iInter (fun _ =>
      isClosed_le (WeakDual.eval_continuous v) continuous_const))
  let A := (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ (n : ℝ)+2}) ∩ U
  have hA : IsCompact A := (weakdual_slice_compact K _ (hslice _)).inter_right hU
  have hout : ∀ f ∈ A, (n : ℝ)+1 < ‖WeakDual.toStrongDual f‖ := by
    intro f hf
    by_contra hn
    obtain ⟨v, hv, hfv⟩ := hD f hf.1.1 (le_of_not_gt hn)
    exact (not_lt_of_ge (hf.2 v hv)) hfv
  obtain ⟨S, hS, hdetect⟩ := compact_dual_finite_detectors A hA ((n : ℝ)+1) (by positivity) hout
  refine ⟨S, hS, ?_⟩
  intro f hf hnorm
  by_cases hOld : ∃ v ∈ D, 1 < f v
  · obtain ⟨v, hv, hfv⟩ := hOld
    exact ⟨v, Finset.mem_union_left S hv, hfv⟩
  · have hu : f ∈ U := by
      intro v hv
      exact le_of_not_gt (fun h => hOld ⟨v, hv, h⟩)
    obtain ⟨v, hv, hfv⟩ := hdetect f ⟨⟨hf, hnorm⟩, hu⟩
    exact ⟨v, Finset.mem_union_right D hv, hfv⟩

/-- Successive compact slices provide finite detector levels whose vector
norms tend to zero, and which together detect the whole dual set. -/
theorem finite_detector_family (K : Set (WeakDual ℝ E))
    (hslice : ∀ r : ℝ, IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}))
    (havoid : ∀ f ∈ K, 1 < ‖WeakDual.toStrongDual f‖) :
    ∃ S : ℕ → Finset E, (∀ n v, v ∈ S n → ‖v‖ ≤ 1 / ((n : ℝ)+1)) ∧
      ∀ f ∈ K, ∃ n v, v ∈ S n ∧ 1 < f v := by
  classical
  let Good : ℕ → Type _ := fun n => {D : Finset E //
    ∀ f ∈ K, ‖WeakDual.toStrongDual f‖ ≤ (n : ℝ)+1 → ∃ v ∈ D, 1 < f v}
  let base : Good 0 := ⟨∅, by
    intro f hf hnorm
    have h := havoid f hf
    norm_num at hnorm
    linarith⟩
  let step : ∀ n, Good n → Good (n+1) := fun n D =>
    ⟨D.val ∪ (finite_detector_step K hslice n D.val D.property).choose, by
      have h := (finite_detector_step K hslice n D.val D.property).choose_spec.2
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h⟩
  let D : ∀ n, Good n := Nat.rec base step
  let S : ℕ → Finset E := fun n => (finite_detector_step K hslice n (D n).val (D n).property).choose
  have hnorm : ∀ n v, v ∈ S n → ‖v‖ ≤ 1 / ((n : ℝ)+1) := fun n =>
    (finite_detector_step K hslice n (D n).val (D n).property).choose_spec.1
  have hsucc : ∀ n, (D (n+1)).val = (D n).val ∪ S n := fun _ => rfl
  have hlevel : ∀ n v, v ∈ (D n).val → ∃ i < n, v ∈ S i := by
    intro n
    induction n with
    | zero =>
      intro v hv
      change v ∈ (∅ : Finset E) at hv
      simp at hv
    | succ n ih =>
      intro v hv
      rw [hsucc] at hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨i, hi, hiv⟩ := ih v hv
        exact ⟨i, Nat.lt_succ_of_lt hi, hiv⟩
      · exact ⟨n, Nat.lt_succ_self n, hv⟩
  refine ⟨S, hnorm, ?_⟩
  intro f hf
  obtain ⟨N, hN⟩ := exists_nat_gt ‖WeakDual.toStrongDual f‖
  obtain ⟨v, hv, hfv⟩ := (D N).property f hf (by linarith)
  obtain ⟨i, _hi, hiv⟩ := hlevel N v hv
  exact ⟨i, v, hiv, hfv⟩

/-- The normalized zero-point case of Krein--Smulian, with its detecting
sequence constructed from the closed bounded slices. -/
theorem zero_not_closure_of_slices_avoiding_unit_ball [CompleteSpace E]
    (K : Set (WeakDual ℝ E)) (hK : Convex ℝ K)
    (hslice : ∀ r : ℝ, IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}))
    (havoid : ∀ f ∈ K, 1 < ‖WeakDual.toStrongDual f‖) :
    (0 : WeakDual ℝ E) ∉ closure K := by
  obtain ⟨S, hS, hdetect⟩ := finite_detector_family K hslice havoid
  obtain ⟨hx, hlim⟩ := finite_family_null_sequence S hS
  apply zero_not_weakstar_closure_of_null_sequence K hK (finiteFamilySequence S) hx hlim
  intro f hf
  obtain ⟨n, v, hv, hfv⟩ := hdetect f hf
  obtain ⟨k, hk⟩ := finiteFamilySequence_covers S n v hv
  exact ⟨k, hk.symm ▸ hfv⟩

#print axioms finite_detector_step
#print axioms finite_detector_family
#print axioms zero_not_closure_of_slices_avoiding_unit_ball
end FTDAP
