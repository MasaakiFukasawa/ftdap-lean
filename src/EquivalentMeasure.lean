import PositiveDensity
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

theorem kreps_yan_normalized_density (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set (WeakClaims P)) (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ f ∈ C, r • f ∈ C)
    (hneg : ∀ f : Lp ℝ ∞ P, 0 ≤ f → weakClaim P (-f) ∈ C)
    (hna : ∀ f ∈ C, 0 ≤ claimValue P f → f = 0) :
    ∃ Z : Lp ℝ 1 P, (∀ᵐ ω ∂P, 0 < Z ω) ∧
      (∫ ω, Z ω ∂P) = 1 ∧ ∀ f ∈ C, claimsPairing P f Z ≤ 0 := by
  obtain ⟨Z, hpos, hsep⟩ := kreps_yan_positive_density P C hconv hclosed hscale hneg hna
  have hint : Integrable (fun ω => Z ω) P := (Lp.memLp Z).integrable (by norm_num)
  have hm : 0 < ∫ ω, Z ω ∂P := by
    apply (integral_pos_iff_support_of_nonneg_ae (hpos.mono (fun _ h => h.le)) hint).mpr
    have he : Function.support (fun ω => Z ω) =ᵐ[P] univ := by
      filter_upwards [hpos] with ω hω
      simp [Function.mem_support, ne_of_gt hω]
    rw [measure_congr he, measure_univ]
    exact zero_lt_one
  let a : ℝ := (∫ ω, Z ω ∂P)⁻¹
  have ha : 0 < a := inv_pos.mpr hm
  refine ⟨a • Z, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul a Z, hpos] with ω hω hp
    rw [hω]
    exact mul_pos ha hp
  · calc
      (∫ ω, (a • Z) ω ∂P) = ∫ ω, a * Z ω ∂P := integral_congr_ae (Lp.coeFn_smul a Z)
      _ = a * ∫ ω, Z ω ∂P := integral_const_mul _ _
      _ = 1 := inv_mul_cancel₀ hm.ne'
  · intro f hf
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ha.le (hsep f hf)

/-- A strictly positive normalized density defines an equivalent probability measure. -/
theorem density_equivalent_probability (P : Measure Ω) [IsFiniteMeasure P] (Z : Lp ℝ 1 P)
    (hpos : ∀ᵐ ω ∂P, 0 < Z ω) (hone : (∫ ω, Z ω ∂P) = 1) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q := by
  let d : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Z ω)
  have hd : Measurable d := Z.val.measurable.ennreal_ofReal
  have hmass : ∫⁻ ω, d ω ∂P = 1 := by
    have hi := ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp Z).integrable (by norm_num)) (hpos.mono (fun _ h => h.le))
    simpa [d, hone] using hi.symm
  refine ⟨⟨?_⟩, withDensity_absolutelyContinuous P d, ?_⟩
  · simpa [withDensity_apply, d] using hmass
  · apply withDensity_absolutelyContinuous' hd.aemeasurable
    filter_upwards [hpos] with ω hω
    exact (ENNReal.ofReal_pos.mpr hω).ne'

#print axioms kreps_yan_normalized_density
#print axioms density_equivalent_probability
end FTDAP
