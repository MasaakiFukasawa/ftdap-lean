import KrepsYan
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω ι : Type*} [MeasurableSpace Ω] [Encodable ι]

/-- A countable family of nonnegative separating densities has a separating
L¹ aggregate whose positive set includes the positive set of every component. -/
theorem aggregate_separating_densities (P : Measure Ω) (C : Set (WeakClaims P))
    (z : ι → Lp ℝ 1 P) (hz : ∀ i, 0 ≤ z i)
    (hsep : ∀ i, ∀ f ∈ C, claimsPairing P f (z i) ≤ 0) :
    ∃ Z : Lp ℝ 1 P, 0 ≤ Z ∧
      (∀ f ∈ C, claimsPairing P f Z ≤ 0) ∧
      ∀ᵐ ω ∂P, ∀ i, 0 < z i ω → 0 < Z ω := by
  let a : ι → ℝ := fun i => (1 / 2 : ℝ) ^ Encodable.encode i / (1 + ‖z i‖)
  have ha : ∀ i, 0 < a i := by intro i; dsimp [a]; positivity
  let term : ι → Lp ℝ 1 P := fun i => a i • z i
  have hnorm : ∀ i, ‖term i‖ ≤ (1 / 2 : ℝ) ^ Encodable.encode i := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ha i)]
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 1 + ‖z i‖)).mpr
    have hp : 0 ≤ (1 / 2 : ℝ) ^ Encodable.encode i := by positivity
    nlinarith [norm_nonneg (z i)]
  have hs : Summable term := summable_geometric_two_encode.of_norm_bounded hnorm
  have hterm : ∀ i, 0 ≤ term i := by
    intro i
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [Lp.coeFn_smul (a i) (z i), (Lp.coeFn_nonneg (z i)).mpr (hz i)] with ω hω hn
    rw [hω]
    exact mul_nonneg (ha i).le hn
  let Z := ∑' i, term i
  refine ⟨Z, tsum_nonneg hterm, ?_, ?_⟩
  · intro f hf
    change claimsPairingCLM P f (∑' i, term i) ≤ 0
    rw [(claimsPairingCLM P f).map_tsum hs]
    apply tsum_nonpos
    intro i
    change claimsPairing P f (a i • z i) ≤ 0
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (ha i).le (hsep i f hf)
  · have hle : ∀ i, term i ≤ Z := fun i => hs.le_tsum i (fun j _ => hterm j)
    have hleAE : ∀ᵐ ω ∂P, ∀ i, term i ω ≤ Z ω :=
      ae_all_iff.mpr (fun i => (Lp.coeFn_le _ _).mpr (hle i))
    have hsmul : ∀ᵐ ω ∂P, ∀ i, term i ω = a i * z i ω :=
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (z i))
    filter_upwards [hleAE, hsmul] with ω hω hsω i hi
    have hp := mul_pos (ha i) hi
    exact hp.trans_le (by simpa [hsω i] using hω i)

#print axioms aggregate_separating_densities
end FTDAP
