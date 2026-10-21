import Pathwise
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp

open MeasureTheory Filter
open scoped Topology
namespace FTDAP

/-- Strictly positive weights cannot erase an exceptional point of a finite jump measure. -/
theorem weighted_null_jumps {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (jumps : Ω → Finset ι) (weight size : Ω → ι → ℝ) (A : Ω → ι → Prop) [∀ ω k, Decidable (A ω k)]
    (hw : ∀ ω k, k ∈ jumps ω → 0 < weight ω k)
    (hs : ∀ ω k, k ∈ jumps ω → 0 < size ω k)
    (hint : Integrable (fun ω => ∑ k ∈ jumps ω,
      weight ω k * (if A ω k then size ω k else 0)) P)
    (hzero : (∫ ω, ∑ k ∈ jumps ω,
      weight ω k * (if A ω k then size ω k else 0) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, ¬ A ω k := by
  classical
  have hn : ∀ ω, 0 ≤ ∑ k ∈ jumps ω,
      weight ω k * (if A ω k then size ω k else 0) := by
    intro ω
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact mul_nonneg (hw ω k hk).le (hs ω k hk).le
    · simp
  have hz := (integral_eq_zero_iff_of_nonneg hn hint).mp hzero
  filter_upwards [hz] with ω hω k hk hA
  have hsingle : weight ω k * size ω k ≤ ∑ j ∈ jumps ω,
      weight ω j * (if A ω j then size ω j else 0) := by
    simpa only [ite_eq_left hA] using Finset.single_le_sum (s := jumps ω)
      (f := fun j => weight ω j * (if A ω j then size ω j else 0))
      (by
        intro j hj
        split_ifs
        · exact mul_nonneg (hw ω j hj).le (hs ω j hj).le
        · simp) hk
  have hp := mul_pos (hw ω k hk) (hs ω k hk)
  simp only [Pi.zero_apply] at hω
  rw [hω] at hsingle
  linarith

/-- The numerical density estimate underlying the uniform L² bound. -/
theorem weighted_L2_density_bound {H : Type*} [NormedAddCommGroup H]
    (g : H) (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (hg : ‖g‖ ≤ c * R) :
    ‖g‖ ^ 2 / (c ^ 2 * R ^ 3) ≤ 1 / R := by
  apply (div_le_div_iff₀ (by positivity : 0 < c ^ 2 * R ^ 3) hR).mpr
  have hsq : ‖g‖ ^ 2 ≤ (c * R) ^ 2 := by
    nlinarith [norm_nonneg g, mul_pos hc hR]
  have hm := mul_le_mul_of_nonneg_right hsq hR.le
  nlinarith

/-- A positive separating density forces a nonnegative separated payoff to vanish. -/
theorem positive_density_separates {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z f : Ω → ℝ) (hZ : ∀ᵐ ω ∂P, 0 < Z ω) (hf : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hi : Integrable (fun ω => Z ω * f ω) P)
    (hsep : (∫ ω, Z ω * f ω ∂P) ≤ 0) : f =ᵐ[P] 0 := by
  have hn : ∀ᵐ ω ∂P, 0 ≤ Z ω * f ω := by
    filter_upwards [hZ, hf] with ω hz hf
    exact mul_nonneg hz.le hf
  have hz : (∫ ω, Z ω * f ω ∂P) = 0 :=
    le_antisymm hsep (integral_nonneg_of_ae hn)
  have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  filter_upwards [hZ, he] with ω hz he
  exact (mul_eq_zero.mp he).resolve_left hz.ne'

#print axioms weighted_null_jumps
#print axioms weighted_L2_density_bound
#print axioms positive_density_separates
end FTDAP
