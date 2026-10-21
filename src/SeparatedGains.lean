import PriceRectangles
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Under the density measure, bounded-claim expectation equals its L1 pairing. -/
theorem density_integral_eq_claims_pairing (P : Measure Ω) (Z : Lp ℝ 1 P)
    (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω) (f : Lp ℝ ∞ P) :
    (∫ ω, f ω ∂P.withDensity (fun ω => ENNReal.ofReal (Z ω))) = claimsPairing P f Z := by
  rw [integral_withDensity_eq_integral_toReal_smul
    (Z.val.measurable.ennreal_ofReal) (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [claimsPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hZ] with ω hω
  rw [ENNReal.toReal_ofReal hω]
  exact mul_comm _ _

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A bounded admissible terminal gain is a bounded claim in the trading cone,
so its density-measure expectation is nonpositive under the actual separator. -/
theorem PriceJumpModel.bounded_gain_separated
    {P : Measure Ω} [IsFiniteMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (Z : Lp ℝ 1 P) (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (hsep : ∀ f ∈ tradingCone P 𝓕 M.active M.times M.marks T, claimsPairing P f Z ≤ 0)
    (H : NNReal × Ω → V) (hH : AdmissibleStrategy P 𝓕 M.active M.times M.marks T H)
    (b : ℝ) (hbound : ∀ᵐ ω ∂P, |finiteJumpGain M.active M.times M.marks H T ω| ≤ b) :
    (∫ ω, finiteJumpGain M.active M.times M.marks H T ω
      ∂P.withDensity (fun ω => ENNReal.ofReal (Z ω))) ≤ 0 := by
  let g := finiteJumpGain M.active M.times M.marks H T
  have hg : Measurable g := (M.gain_adapted H hH.1 T).mono (𝓕.le T) le_rfl
  have hmem : MemLp g ∞ P := MemLp.of_bound hg.aestronglyMeasurable b
    (by simpa only [Real.norm_eq_abs] using hbound)
  let f := hmem.toLp g
  have hf : weakClaim P f ∈ tradingCone P 𝓕 M.active M.times M.marks T := by
    refine ⟨H, hH, ?_⟩
    filter_upwards [hmem.coeFn_toLp] with ω hω
    change f ω ≤ g ω
    exact hω.le
  have hQ := withDensity_absolutelyContinuous P (fun ω => ENNReal.ofReal (Z ω))
  have he := hQ.ae_eq hmem.coeFn_toLp
  calc
    (∫ ω, g ω ∂P.withDensity (fun ω => ENNReal.ofReal (Z ω))) =
        ∫ ω, f ω ∂P.withDensity (fun ω => ENNReal.ofReal (Z ω)) := integral_congr_ae he.symm
    _ = claimsPairing P f Z := density_integral_eq_claims_pairing P Z hZ f
    _ ≤ 0 := hsep _ hf

#print axioms density_integral_eq_claims_pairing
#print axioms PriceJumpModel.bounded_gain_separated
end FTDAP
