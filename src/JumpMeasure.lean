import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory Filter
open scoped ENNReal
namespace FTDAP
variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A countable enumeration of weighted random atoms defines a measure on the target sigma algebra.
The target can in particular carry the predictable sigma algebra. -/
noncomputable def jumpMeasure (P : Measure Ω) (atom : ℕ → Ω → α)
    (weight : ℕ → Ω → ℝ≥0∞) : Measure α :=
  Measure.sum (fun n => (P.withDensity (weight n)).map (atom n))

/-- The actual integration formula, rather than an assumed measure-construction property. -/
theorem lintegral_jumpMeasure (P : Measure Ω) (atom : ℕ → Ω → α)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n)) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂jumpMeasure P atom weight) =
      ∑' n, ∫⁻ ω, weight n ω * f (atom n ω) ∂P := by
  rw [jumpMeasure, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_map hf (ha n)]
  exact lintegral_withDensity_eq_lintegral_mul P (hw n) (hf.comp (ha n))

/-- Finiteness follows from an integrable mass bound on the random atom weights. -/
theorem jumpMeasure_mass (P : Measure Ω) (atom : ℕ → Ω → α)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n)) :
    jumpMeasure P atom weight Set.univ = ∫⁻ ω, ∑' n, weight n ω ∂P := by
  rw [← lintegral_one]
  rw [lintegral_jumpMeasure P atom weight ha hw (fun _ => 1) measurable_const]
  simp only [mul_one]
  exact (lintegral_tsum (fun n => (hw n).aemeasurable)).symm

theorem jumpMeasure_mass_le (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (K : ℝ≥0∞) (hK : ∀ᵐ ω ∂P, ∑' n, weight n ω ≤ K) :
    jumpMeasure P atom weight Set.univ ≤ K := by
  rw [jumpMeasure_mass P atom weight ha hw]
  have h := lintegral_mono_ae hK
  simpa using h

/-- The exact AE transport used to recover simultaneous convergence at all actual jumps. -/
theorem ae_jumpMeasure_iff (P : Measure Ω) (atom : ℕ → Ω → α)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n)) (p : α → Prop) (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂jumpMeasure P atom weight, p x) ↔
      ∀ᵐ ω ∂P, ∀ n, weight n ω ≠ 0 → p (atom n ω) := by
  rw [jumpMeasure, Measure.ae_sum_iff, ae_all_iff]
  apply forall_congr'
  intro n
  rw [ae_map_iff (ha n).aemeasurable hp, ae_withDensity_iff (hw n)]

/-- Forward transport does not require measurability of the predicate itself. -/
theorem ae_at_jump_atoms (P : Measure Ω) (atom : ℕ → Ω → α)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n)) (p : α → Prop)
    (hp : ∀ᵐ x ∂jumpMeasure P atom weight, p x) :
    ∀ᵐ ω ∂P, ∀ n, weight n ω ≠ 0 → p (atom n ω) := by
  apply ae_all_iff.mpr
  intro n
  apply (ae_withDensity_iff (hw n)).mp
  apply ae_of_ae_map (ha n).aemeasurable
  exact (Measure.ae_sum_iff.mp hp) n

#print axioms lintegral_jumpMeasure
#print axioms ae_jumpMeasure_iff
end FTDAP
