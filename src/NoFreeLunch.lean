import EquivalentMeasure
import MeasureSteps

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A positive L¹ separator excludes positive claims from the actual weak-star
closure of a cone, giving NFL rather than only NA. -/
theorem positive_separator_no_free_lunch (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set (WeakClaims P)) (Z : Lp ℝ 1 P)
    (hpos : ∀ᵐ ω ∂P, 0 < Z ω)
    (hsep : ∀ f ∈ C, claimsPairing P f Z ≤ 0) :
    ∀ f ∈ closure C, 0 ≤ claimValue P f → f = 0 := by
  have hclosed : IsClosed {f : WeakClaims P | claimsPairing P f Z ≤ 0} :=
    isClosed_le (WeakBilin.eval_continuous (claimsPairing P) Z) continuous_const
  have hclosure := closure_minimal hsep hclosed
  intro f hf hn
  have hi : Integrable (fun ω => Z ω * claimValue P f ω) P :=
    (Lp.memLp Z).integrable_mul (Lp.memLp (claimValue P f))
  have hz : claimValue P f =ᵐ[P] (0 : Ω → ℝ) := by
    apply positive_density_separates P (fun ω => Z ω) (fun ω => claimValue P f ω)
      hpos ((Lp.coeFn_nonneg _).mpr hn) hi
    have hs := hclosure hf
    change claimsPairing P (claimValue P f) Z ≤ 0 at hs
    rw [claimsPairing_eq_integral] at hs
    simpa only [mul_comm] using hs
  have he : claimValue P f = (0 : Lp ℝ ∞ P) := by
    apply Lp.ext
    exact hz.trans (Lp.coeFn_zero ℝ ∞ P).symm
  exact he

/-- The full functional-analytic NFL/separating-density equivalence for a
convex cone containing all nonpositive bounded claims. -/
theorem no_free_lunch_iff_positive_separator (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set (WeakClaims P)) (hconv : Convex ℝ C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ f ∈ C, r • f ∈ C)
    (hneg : ∀ f : Lp ℝ ∞ P, 0 ≤ f → weakClaim P (-f) ∈ C) :
    (∀ f ∈ closure C, 0 ≤ claimValue P f → f = 0) ↔
    ∃ Z : Lp ℝ 1 P, (∀ᵐ ω ∂P, 0 < Z ω) ∧
      (∫ ω, Z ω ∂P) = 1 ∧ ∀ f ∈ C, claimsPairing P f Z ≤ 0 := by
  constructor
  · intro hna
    have hsc : ∀ r : ℝ, 0 ≤ r → ∀ f ∈ closure C, r • f ∈ closure C := by
      intro r hr f hf
      exact map_mem_closure (continuous_const_smul r) hf (fun g hg => hscale r hr g hg)
    obtain ⟨Z, hp, h1, hs⟩ := kreps_yan_normalized_density P (closure C)
      hconv.closure isClosed_closure hsc
      (fun f hf => subset_closure (hneg f hf)) hna
    exact ⟨Z, hp, h1, fun f hf => hs f (subset_closure hf)⟩
  · rintro ⟨Z, hp, _, hs⟩
    exact positive_separator_no_free_lunch P C Z hp hs

#print axioms positive_separator_no_free_lunch
#print axioms no_free_lunch_iff_positive_separator
end FTDAP
