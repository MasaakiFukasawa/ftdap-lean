import WeakStar
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def claimIndicator (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) : Lp ℝ ∞ P :=
  indicatorConstLp ∞ hA (measure_ne_top P A) (1 : ℝ)

theorem claimIndicator_nonneg (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) : 0 ≤ claimIndicator P A hA := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [indicatorConstLp_coeFn (p := ∞) (hs := hA) (hμs := measure_ne_top P A) (c := (1 : ℝ))] with ω hω
  change 0 ≤ claimIndicator P A hA ω
  rw [claimIndicator, hω]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω

theorem claimsPairing_indicator (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (z : Lp ℝ 1 P) :
    claimsPairing P (claimIndicator P A hA) z = ∫ ω in A, z ω ∂P := by
  rw [claimsPairing_eq_integral, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := ∞) (hs := hA) (hμs := measure_ne_top P A) (c := (1 : ℝ))] with ω hω
  change claimIndicator P A hA ω * z ω = A.indicator (fun ω => z ω) ω
  rw [claimIndicator, hω]
  by_cases h : ω ∈ A <;> simp [Set.indicator, h]

/-- The first, event-by-event separation step of Kreps–Yan, on the actual L∞/L¹ pair. -/
theorem kreps_yan_event_separator (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set (WeakClaims P)) (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ f ∈ C, r • f ∈ C)
    (hneg : ∀ f : Lp ℝ ∞ P, 0 ≤ f → weakClaim P (-f) ∈ C)
    (hna : ∀ f ∈ C, 0 ≤ claimValue P f → f = 0)
    (A : Set Ω) (hA : MeasurableSet A) (hpos : P A ≠ 0) :
    ∃ z : Lp ℝ 1 P, 0 ≤ z ∧ 0 < ∫ ω in A, z ω ∂P ∧
      ∀ f ∈ C, claimsPairing P f z ≤ 0 := by
  have hzero : (0 : WeakClaims P) ∈ C := by
    change weakClaim P (0 : Lp ℝ ∞ P) ∈ C
    simpa [weakClaim] using hneg 0 le_rfl
  have hx : weakClaim P (claimIndicator P A hA) ∉ C := by
    intro hx
    have heq := congrArg (claimValue P) (hna _ hx (claimIndicator_nonneg P A hA))
    change claimIndicator P A hA = (0 : Lp ℝ ∞ P) at heq
    have hn : ‖claimIndicator P A hA‖ = 1 := by
      simpa [claimIndicator] using norm_indicatorConstLp_top (hs := hA) (hμs := measure_ne_top P A) (c := (1 : ℝ)) hpos
    rw [heq, norm_zero] at hn
    norm_num at hn
  obtain ⟨z, hzA, hzC⟩ := weakstar_cone_separator P C hconv hclosed hzero hscale _ hx
  have hi : Integrable (fun ω => z ω) P := (Lp.memLp z).integrable (by norm_num)
  have hn : 0 ≤ᵐ[P] (fun ω => z ω) := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hi
    intro B hB hPB
    have h := hzC (weakClaim P (-claimIndicator P B hB)) (hneg _ (claimIndicator_nonneg P B hB))
    change claimsPairing P (-claimIndicator P B hB) z ≤ 0 at h
    rw [map_neg, LinearMap.neg_apply, claimsPairing_indicator] at h
    linarith
  refine ⟨z, (Lp.coeFn_nonneg z).mp hn, ?_, hzC⟩
  change 0 < claimsPairing P (claimIndicator P A hA) z at hzA
  rwa [claimsPairing_indicator] at hzA

#print axioms kreps_yan_event_separator
end FTDAP
