import JumpMeasure
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal
namespace FTDAP
variable {Ω α V : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [NormedAddCommGroup V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V]

/-- A pathwise weighted energy bound gives square integrability for the jump measure. -/
theorem weighted_portfolio_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (H : α → V) (hH : Measurable H) (B : ℝ≥0∞) (hB : B < ∞)
    (henergy : ∀ᵐ ω ∂P,
      ∑' n, weight n ω * ENNReal.ofReal (‖H (atom n ω)‖ ^ 2) ≤ B) :
    MemLp H 2 (jumpMeasure P atom weight) := by
  have hm : Measurable (fun x => ENNReal.ofReal (‖H x‖ ^ 2)) :=
    hH.norm.pow_const 2 |>.ennreal_ofReal
  have he : (∫⁻ x, ENNReal.ofReal (‖H x‖ ^ 2) ∂jumpMeasure P atom weight) ≤ B := by
    rw [lintegral_jumpMeasure P atom weight ha hw _ hm]
    have ht := lintegral_tsum (μ := P)
      (f := fun n ω => weight n ω * ENNReal.ofReal (‖H (atom n ω)‖ ^ 2))
      (fun n => ((hw n).mul (hm.comp (ha n))).aemeasurable)
    rw [← ht]
    simpa using lintegral_mono_ae henergy
  apply (memLp_two_iff_integrable_sq_norm hH.aestronglyMeasurable).mpr
  refine ⟨(hH.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => sq_nonneg ‖H x‖))).mpr
  exact lt_of_le_of_lt he hB

omit [SecondCountableTopology V] in
/-- The energy estimate also bounds the integral of the squared portfolio norm. -/
theorem weighted_portfolio_energy_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (H : α → V) (hH : Measurable H) (B : ℝ≥0∞) (hB : B < ∞)
    (henergy : ∀ᵐ ω ∂P,
      ∑' n, weight n ω * ENNReal.ofReal (‖H (atom n ω)‖ ^ 2) ≤ B) :
    (∫ x, ‖H x‖ ^ 2 ∂jumpMeasure P atom weight) ≤ B.toReal := by
  have hm : Measurable (fun x => ENNReal.ofReal (‖H x‖ ^ 2)) :=
    hH.norm.pow_const 2 |>.ennreal_ofReal
  have he : (∫⁻ x, ENNReal.ofReal (‖H x‖ ^ 2) ∂jumpMeasure P atom weight) ≤ B := by
    rw [lintegral_jumpMeasure P atom weight ha hw _ hm]
    have ht := lintegral_tsum (μ := P)
      (f := fun n ω => weight n ω * ENNReal.ofReal (‖H (atom n ω)‖ ^ 2))
      (fun n => ((hw n).mul (hm.comp (ha n))).aemeasurable)
    rw [← ht]
    simpa using lintegral_mono_ae henergy
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖H x‖))
    (hH.norm.pow_const 2).aestronglyMeasurable]
  exact ENNReal.toReal_mono hB.ne he

/-- The same estimate is the Hilbert norm bound required by convex averaging. -/
theorem weighted_portfolio_lp_norm_bound [InnerProductSpace ℝ V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (H : α → V) (hH : Measurable H) (B : ℝ≥0∞) (hB : B < ∞)
    (henergy : ∀ᵐ ω ∂P,
      ∑' n, weight n ω * ENNReal.ofReal (‖H (atom n ω)‖ ^ 2) ≤ B) :
    ‖(weighted_portfolio_memLp P atom weight ha hw H hH B hB henergy).toLp H‖ ^ 2
      ≤ B.toReal := by
  let hL := weighted_portfolio_memLp P atom weight ha hw H hH B hB henergy
  have he : ‖hL.toLp H‖ ^ 2 =
      ∫ x, ‖H x‖ ^ 2 ∂jumpMeasure P atom weight := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hL.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  rw [he]
  exact weighted_portfolio_energy_bound P atom weight ha hw H hH B hB henergy

#print axioms weighted_portfolio_memLp
#print axioms weighted_portfolio_energy_bound
#print axioms weighted_portfolio_lp_norm_bound
end FTDAP
