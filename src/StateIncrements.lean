import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Set.Finite.Basic

open Set Bornology Filter
open scoped Topology
namespace FTDAP
variable {V : Type*} [NormedAddCommGroup V]

/-- Local finiteness gives a deterministic finite set containing every increment
between two price states satisfying a deterministic stopped bound. -/
theorem locally_finite_bounded_increments (E : Set V)
    (hfinite : ∀ B : Set V, IsBounded B → (E ∩ B).Finite) (b : ℝ) :
    ∃ F : Finset V, ∀ x y, x ∈ E → y ∈ E → ‖x‖ ≤ b → ‖y‖ ≤ b → y - x ∈ F := by
  classical
  let K := E ∩ Metric.closedBall (0 : V) b
  have hK : K.Finite := hfinite _ Metric.isBounded_closedBall
  let A := hK.toFinset
  refine ⟨(A ×ˢ A).image (fun p => p.2 - p.1), ?_⟩
  intro x y hx hy hxb hyb
  apply Finset.mem_image.mpr
  refine ⟨(x, y), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
  · exact hK.mem_toFinset.mpr ⟨hx, by simpa using hxb⟩
  · exact hK.mem_toFinset.mpr ⟨hy, by simpa using hyb⟩

/-- The finite increment sets can be chosen simultaneously for every localizer. -/
theorem locally_finite_localizing_increments (E : Set V)
    (hfinite : ∀ B : Set V, IsBounded B → (E ∩ B).Finite) (b : ℕ → ℝ) :
    ∃ F : ℕ → Finset V, ∀ m x y, x ∈ E → y ∈ E →
      ‖x‖ ≤ b m → ‖y‖ ≤ b m → y - x ∈ F m := by
  choose F hF using fun m => locally_finite_bounded_increments E hfinite (b m)
  exact ⟨F, hF⟩

/-- Left limits of bounded states remain in the same finite set of states. -/
theorem finite_state_limit {β : Type*} (l : Filter β) [NeBot l]
    (E : Set V) (hfinite : ∀ B : Set V, IsBounded B → (E ∩ B).Finite)
    (b : ℝ) (f : β → V) (x : V) (hf : Tendsto f l (𝓝 x))
    (hstates : ∀ᶠ u in l, f u ∈ E ∧ ‖f u‖ ≤ b) :
    x ∈ E ∧ ‖x‖ ≤ b := by
  have hK := hfinite (Metric.closedBall (0 : V) b) Metric.isBounded_closedBall
  have he : ∀ᶠ u in l, f u ∈ E ∩ Metric.closedBall (0 : V) b := by
    filter_upwards [hstates] with u hu
    exact ⟨hu.1, by simpa using hu.2⟩
  have hx := hK.isClosed.mem_of_tendsto hf he
  exact ⟨hx.1, by simpa using hx.2⟩

/-- A bounded post-jump state and its bounded left limit give a finite increment. -/
theorem locally_finite_limit_increments (E : Set V)
    (hfinite : ∀ B : Set V, IsBounded B → (E ∩ B).Finite) (b : ℝ) :
    ∃ F : Finset V, ∀ {β : Type} (l : Filter β) [NeBot l]
      (f : β → V) (x y : V), Tendsto f l (𝓝 x) →
      (∀ᶠ u in l, f u ∈ E ∧ ‖f u‖ ≤ b) →
      y ∈ E → ‖y‖ ≤ b → y - x ∈ F := by
  obtain ⟨F, hF⟩ := locally_finite_bounded_increments E hfinite b
  refine ⟨F, ?_⟩
  intro β l hl f x y hf hs hy hyb
  obtain ⟨hx, hxb⟩ := finite_state_limit l E hfinite b f x hf hs
  exact hF x y hx hy hxb hyb

#print axioms finite_state_limit
#print axioms locally_finite_limit_increments
#print axioms locally_finite_bounded_increments
#print axioms locally_finite_localizing_increments
end FTDAP
