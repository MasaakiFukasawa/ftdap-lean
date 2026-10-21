import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open MeasureTheory Set
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def claimsPairingCLM (P : Measure Ω) :
    Lp ℝ ∞ P →L[ℝ] Lp ℝ 1 P →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing P ∞ 1

noncomputable def claimsPairing (P : Measure Ω) :
    Lp ℝ ∞ P →ₗ[ℝ] Lp ℝ 1 P →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp (claimsPairingCLM P).toLinearMap

/-- Claims equipped with precisely σ(L∞,L¹), not their norm topology. -/
abbrev WeakClaims (P : Measure Ω) := WeakBilin (claimsPairing P)

def claimValue (P : Measure Ω) (f : WeakClaims P) : Lp ℝ ∞ P := f

def weakClaim (P : Measure Ω) (f : Lp ℝ ∞ P) : WeakClaims P := f

theorem claimsPairing_eq_integral (P : Measure Ω) (f : Lp ℝ ∞ P) (z : Lp ℝ 1 P) :
    claimsPairing P f z = ∫ ω, f ω * z ω ∂P := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing_eq_integral f z

/-- Closed convex cones in the actual weak-star claim space have L¹ separators.
Both weak-star separation and its representation by an L¹ density are proved here. -/
theorem weakstar_cone_separator (P : Measure Ω) (C : Set (WeakClaims P))
    (hconv : Convex ℝ C) (hclosed : IsClosed C) (hzero : 0 ∈ C)
    (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ f ∈ C, r • f ∈ C)
    (x : WeakClaims P) (hx : x ∉ C) :
    ∃ z : Lp ℝ 1 P, 0 < claimsPairing P x z ∧
      ∀ f ∈ C, claimsPairing P f z ≤ 0 := by
  obtain ⟨L, b, hC, hxL⟩ := geometric_hahn_banach_closed_point hconv hclosed hx
  have hb : 0 < b := by simpa using hC 0 hzero
  have hnonpos : ∀ f ∈ C, L f ≤ 0 := by
    intro f hf
    by_contra hn
    have hp : 0 < L f := lt_of_not_ge hn
    let r := (b + 1) / L f
    have hr : 0 ≤ r := div_nonneg (by linarith) hp.le
    have h := hC (r • f) (hscale r hr f hf)
    rw [map_smul, smul_eq_mul] at h
    have he : r * L f = b + 1 := by
      dsimp [r]
      exact div_mul_cancel₀ _ hp.ne'
    rw [he] at h
    linarith
  obtain ⟨z, hz⟩ := LinearMap.dualEmbedding_surjective (claimsPairing P) L
  have he : ∀ f : WeakClaims P, L f = claimsPairing P f z := by
    intro f
    rw [← hz]
    rfl
  refine ⟨z, ?_, ?_⟩
  · rw [← he x]
    exact hb.trans hxL
  · intro f hf
    rw [← he f]
    exact hnonpos f hf

#print axioms weakstar_cone_separator
end FTDAP
