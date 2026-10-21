import L1DualPreparation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Indicator tests bound the Hilbert representative of an L1 functional
above by its operator norm. -/
theorem l1_hilbert_representative_upper_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 1 P →L[ℝ] ℝ) (Y : Lp ℝ 2 P)
    (hrep : ∀ g : Lp ℝ 2 P, L (l2ToL1 P g) = ⟪Y, g⟫) :
    ∀ᵐ ω ∂P, Y ω ≤ ‖L‖ := by
  have hYi : Integrable (fun ω => Y ω) P := (Lp.memLp Y).integrable (by norm_num)
  apply ae_le_of_forall_setIntegral_le hYi (integrable_const ‖L‖)
  intro A hA _hPA
  let φ : Ω → ℝ := A.indicator (fun _ => 1)
  have hφm : Measurable φ := measurable_const.indicator hA
  have hφb : ∀ ω, ‖φ ω‖ ≤ 1 := by
    intro ω
    by_cases h : ω ∈ A <;> simp [φ, h]
  have hφ : MemLp φ 2 P := MemLp.of_bound hφm.aestronglyMeasurable 1 (Eventually.of_forall hφb)
  let g := hφ.toLp φ
  have hpair : L (l2ToL1 P g) = ∫ ω in A, Y ω ∂P := by
    rw [hrep g, L2.inner_def, ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with ω hω
    change inner ℝ (Y ω) (g ω) = A.indicator (fun ω => Y ω) ω
    rw [hω]
    by_cases h : ω ∈ A <;> simp [φ, h]
  have hnorm : ‖l2ToL1 P g‖ = ∫ ω in A, (1 : ℝ) ∂P := by
    rw [L1.norm_eq_integral_norm, ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [hφ.coeFn_toLp] with ω hω
    change ‖g ω‖ = A.indicator (fun _ => (1 : ℝ)) ω
    rw [hω]
    by_cases h : ω ∈ A <;> simp [φ, h]
  rw [← hpair]
  calc
    L (l2ToL1 P g) ≤ |L (l2ToL1 P g)| := le_abs_self _
    _ ≤ ‖L‖ * ‖l2ToL1 P g‖ := L.le_opNorm _
    _ = ‖L‖ * ∫ ω in A, (1 : ℝ) ∂P := by rw [hnorm]
    _ = ∫ ω in A, ‖L‖ ∂P := by rw [← integral_const_mul]; simp

/-- Applying the indicator argument to both signs makes the representative
essentially bounded, which supplies an actual L-infinity claim. -/
theorem l1_hilbert_representative_abs_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 1 P →L[ℝ] ℝ) (Y : Lp ℝ 2 P)
    (hrep : ∀ g : Lp ℝ 2 P, L (l2ToL1 P g) = ⟪Y, g⟫) :
    ∀ᵐ ω ∂P, |Y ω| ≤ ‖L‖ := by
  have hup := l1_hilbert_representative_upper_bound P L Y hrep
  have hrepneg : ∀ g : Lp ℝ 2 P, (-L) (l2ToL1 P g) = ⟪-Y, g⟫ := by
    intro g
    simpa only [neg_apply, inner_neg_left] using congrArg Neg.neg (hrep g)
  have hlow := l1_hilbert_representative_upper_bound P (-L) (-Y) hrepneg
  filter_upwards [hup, hlow, Lp.coeFn_neg Y] with ω hu hl he
  rw [he, norm_neg] at hl
  change -Y ω ≤ ‖L‖ at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

#print axioms l1_hilbert_representative_upper_bound
#print axioms l1_hilbert_representative_abs_bound
end FTDAP
