import ClaimSliceClosed
import WeakStar
import Mathlib.Analysis.InnerProductSpace.Dual

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def claimInL2 (P : Measure Ω) [IsFiniteMeasure P] (f : Lp ℝ ∞ P) : Lp ℝ 2 P :=
  ((Lp.memLp f).mono_exponent le_top).toLp f

noncomputable def densityFromL2 (P : Measure Ω) [IsFiniteMeasure P] (g : Lp ℝ 2 P) : Lp ℝ 1 P :=
  ((Lp.memLp g).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).toLp g

theorem pairing_densityFromL2 (P : Measure Ω) [IsFiniteMeasure P]
    (f : Lp ℝ ∞ P) (g : Lp ℝ 2 P) :
    claimsPairing P f (densityFromL2 P g) = ⟪g, claimInL2 P f⟫ := by
  rw [claimsPairing_eq_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp f).mono_exponent (p := 2) le_top).coeFn_toLp,
    ((Lp.memLp g).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).coeFn_toLp]
    with ω hf hg
  rw [show densityFromL2 P g ω = g ω from hg, show claimInL2 P f ω = f ω from hf]
  simp

/-- Closed convex L² claim sets induce weak-star closed sets of bounded claims.
The Hilbert separator is represented explicitly by an L¹ density. -/
theorem l2_closed_convex_weakstar_closed (P : Measure Ω) [IsFiniteMeasure P]
    (K : Set (Lp ℝ 2 P)) (hconv : Convex ℝ K) (hclosed : IsClosed K) :
    IsClosed {f : WeakClaims P | claimInL2 P (claimValue P f) ∈ K} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  have hxK : claimInL2 P (claimValue P x) ∉ K := hx
  obtain ⟨L, b, hK, hxL⟩ := geometric_hahn_banach_closed_point hconv hclosed hxK
  let g : Lp ℝ 2 P := (InnerProductSpace.toDual ℝ (Lp ℝ 2 P)).symm L
  have he : ∀ f : Lp ℝ ∞ P, claimsPairing P f (densityFromL2 P g) = L (claimInL2 P f) := by
    intro f
    rw [pairing_densityFromL2]
    exact InnerProductSpace.toDual_symm_apply
  let U : Set (WeakClaims P) := {f | b < claimsPairing P f (densityFromL2 P g)}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const (WeakBilin.eval_continuous (claimsPairing P) (densityFromL2 P g))
  refine ⟨U, ?_, hUopen, ?_⟩
  · intro f hf hfK
    have hlow : b < L (claimInL2 P (claimValue P f)) := by
      change b < claimsPairing P (claimValue P f) (densityFromL2 P g) at hf
      rwa [he] at hf
    exact (not_lt_of_ge hlow.le) (hK _ hfK)
  · change b < claimsPairing P (claimValue P x) (densityFromL2 P g)
    rwa [he]

#print axioms pairing_densityFromL2
#print axioms l2_closed_convex_weakstar_closed
end FTDAP
