import ForwardFTAP
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A deterministic bound on the pathwise total atom weight gives finite mass. -/
theorem nonnegative_atomic_measure_mass_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (ha : ∀ n, Measurable (atom n))
    (w : ℕ → Ω → ℝ) (hw : ∀ n, Measurable (w n)) (hwpos : ∀ n ω, 0 ≤ w n ω)
    (J : Ω → Finset ℕ) (hsupport : ∀ ω n, n ∉ J ω → w n ω = 0)
    (K : ℝ) (hmass : ∀ᵐ ω ∂P, (∑ n ∈ J ω, w n ω) ≤ K) :
    jumpMeasure P atom (fun n ω => ENNReal.ofReal (w n ω)) univ ≤ ENNReal.ofReal K := by
  apply jumpMeasure_mass_le P atom _ ha (fun n => (hw n).ennreal_ofReal)
  filter_upwards [hmass] with ω hω
  rw [tsum_eq_sum (s := J ω) (fun n hn => by rw [hsupport ω n hn, ENNReal.ofReal_zero])]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hwpos n ω)]
  exact ENNReal.ofReal_le_ofReal hω

/-- Integration of bounded functions against a finite random-atom measure is
expectation of the actual pathwise finite sum. Both exchanges of integration
and countable summation are proved from the uniform mass bound. -/
theorem integral_finite_jump_measure
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (ha : ∀ n, Measurable (atom n))
    (w : ℕ → Ω → ℝ) (hw : ∀ n, Measurable (w n)) (hwpos : ∀ n ω, 0 ≤ w n ω)
    (J : Ω → Finset ℕ) (hsupport : ∀ ω n, n ∉ J ω → w n ω = 0)
    (K : ℝ) (hmass : ∀ᵐ ω ∂P, (∑ n ∈ J ω, w n ω) ≤ K)
    (H : α → ℝ) (hH : Measurable H) (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ x, |H x| ≤ B) :
    (∫ x, H x ∂jumpMeasure P atom (fun n ω => ENNReal.ofReal (w n ω))) =
      ∫ ω, ∑ n ∈ J ω, w n ω * H (atom n ω) ∂P := by
  classical
  let μ := jumpMeasure P atom (fun n ω => ENNReal.ofReal (w n ω))
  have hmassE : ∀ᵐ ω ∂P, (∑' n, ENNReal.ofReal (w n ω)) ≤ ENNReal.ofReal K := by
    filter_upwards [hmass] with ω hω
    rw [tsum_eq_sum (s := J ω) (fun n hn => by rw [hsupport ω n hn, ENNReal.ofReal_zero])]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => hwpos n ω)]
    exact ENNReal.ofReal_le_ofReal hω
  have hμmass : μ univ ≤ ENNReal.ofReal K :=
    jumpMeasure_mass_le P atom _ ha (fun n => (hw n).ennreal_ofReal) _ hmassE
  let : IsFiniteMeasure μ := ⟨hμmass.trans_lt ENNReal.ofReal_lt_top⟩
  have hHint : Integrable H μ :=
    (show MemLp H 1 μ from MemLp.of_bound hH.aestronglyMeasurable B
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hHb x))).integrable le_rfl
  have hsumdom : ∀ ω, (∑' n, B * w n ω) = B * ∑ n ∈ J ω, w n ω := by
    intro ω
    rw [tsum_eq_sum (s := J ω) (fun n hn => by rw [hsupport ω n hn, mul_zero]), Finset.mul_sum]
  have hdommeas : Measurable (fun ω => ∑' n, B * w n ω) :=
    Measurable.tsum (fun n => measurable_const.mul (hw n))
  have hdomint : Integrable (fun ω => ∑' n, B * w n ω) P := by
    apply (show MemLp _ 1 P from MemLp.of_bound hdommeas.aestronglyMeasurable (B*K) ?_).integrable le_rfl
    filter_upwards [hmass] with ω hω
    rw [hsumdom, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hB (Finset.sum_nonneg (fun n _ => hwpos n ω)))]
    exact mul_le_mul_of_nonneg_left hω hB
  have hseries := hasSum_integral_of_dominated_convergence (fun n ω => B * w n ω)
    (fun n => ((hw n).mul (hH.comp (ha n))).aestronglyMeasurable)
    (fun n => Eventually.of_forall (fun ω => by
      change ‖w n ω * H (atom n ω)‖ ≤ B * w n ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwpos n ω)]
      nlinarith [mul_le_mul_of_nonneg_left (hHb (atom n ω)) (hwpos n ω)]))
    (Eventually.of_forall (fun ω =>
      (hasSum_sum_of_ne_finset_zero (fun n hn => by rw [hsupport ω n hn, mul_zero])).summable))
    hdomint (Eventually.of_forall (fun ω =>
      hasSum_sum_of_ne_finset_zero (fun n hn => by
        change w n ω * H (atom n ω) = 0
        rw [hsupport ω n hn, zero_mul])))
  calc
    (∫ x, H x ∂μ) = ∑' n, ∫ x, H x ∂(P.withDensity (fun ω => ENNReal.ofReal (w n ω))).map (atom n) :=
      integral_sum_measure hHint
    _ = ∑' n, ∫ ω, w n ω * H (atom n ω) ∂P := by
      apply tsum_congr
      intro n
      rw [integral_map (ha n).aemeasurable hH.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul (hw n).ennreal_ofReal
          (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by
        change (ENNReal.ofReal (w n ω)).toReal • H (atom n ω) = w n ω * H (atom n ω)
        rw [ENNReal.toReal_ofReal (hwpos n ω)]
        rfl)
    _ = ∫ ω, ∑ n ∈ J ω, w n ω * H (atom n ω) ∂P := hseries.tsum_eq

/-- Bounded predictable integrands and a bounded sum of absolute atom marks
make the actual finite signed sum integrable. Random support is handled by a
countable measurable sum rather than an assumed measurable enumeration. -/
theorem bounded_signed_atomic_sum_integrable
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (ha : ∀ n, Measurable (atom n))
    (d : ℕ → Ω → ℝ) (hd : ∀ n, Measurable (d n))
    (J : Ω → Finset ℕ) (hsupport : ∀ ω n, n ∉ J ω → d n ω = 0)
    (K : ℝ) (hmass : ∀ᵐ ω ∂P, (∑ n ∈ J ω, |d n ω|) ≤ K)
    (H : α → ℝ) (hH : Measurable H) (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ x, |H x| ≤ B) :
    Integrable (fun ω => ∑ n ∈ J ω, d n ω * H (atom n ω)) P := by
  classical
  have hmeas : Measurable (fun ω => ∑ n ∈ J ω, d n ω * H (atom n ω)) := by
    have hm : Measurable (fun ω => ∑' n, d n ω * H (atom n ω)) :=
      Measurable.tsum (fun n => (hd n).mul (hH.comp (ha n)))
    have he : (fun ω => ∑' n, d n ω * H (atom n ω)) =
        (fun ω => ∑ n ∈ J ω, d n ω * H (atom n ω)) := by
      funext ω
      exact tsum_eq_sum (fun n hn => by rw [hsupport ω n hn, zero_mul])
    rwa [he] at hm
  apply (show MemLp _ 1 P from MemLp.of_bound hmeas.aestronglyMeasurable (B*K) ?_).integrable le_rfl
  filter_upwards [hmass] with ω hω
  calc
    ‖∑ n ∈ J ω, d n ω * H (atom n ω)‖ ≤ ∑ n ∈ J ω, ‖d n ω * H (atom n ω)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ J ω, B * |d n ω| := by
      apply Finset.sum_le_sum
      intro n _
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hHb (atom n ω)) (abs_nonneg (d n ω))]
    _ = B * ∑ n ∈ J ω, |d n ω| := (Finset.mul_sum _ _ _).symm
    _ ≤ B*K := mul_le_mul_of_nonneg_left hω hB

#print axioms nonnegative_atomic_measure_mass_le
#print axioms bounded_signed_atomic_sum_integrable
#print axioms integral_finite_jump_measure
end FTDAP
