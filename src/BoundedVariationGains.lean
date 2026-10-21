import BoundedVariationCoordinateGains
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

omit [MeasurableSpace Ω] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Finite portfolio sums give finite sums of their actual gains. -/
theorem finite_gain_finset_sum {ι : Type*} (I : Finset ι)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → NNReal) (Δ : ℕ → Ω → V)
    (H : ι → NNReal × Ω → V) (t : NNReal) (ω : Ω) :
    finiteJumpGain jumps τ Δ (∑ i ∈ I, H i) t ω =
      ∑ i ∈ I, finiteJumpGain jumps τ Δ (H i) t ω := by
  classical
  unfold finiteJumpGain
  simp only [Finset.sum_apply, sum_inner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : τ k ω ≤ t <;> simp [ht]

/-- Bounded predictable vector portfolios have zero expected gain for a
finite-dimensional martingale with bounded total jump variation. -/
theorem PriceJumpModel.bounded_variation_gain [FiniteDimensional ℝ V]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (hmart : Martingale (fun (t : Iic T) => S t.val) (horizonFiltration 𝓕 T) P)
    (K : ℝ) (hvar : ∀ᵐ ω ∂P, (∑ k ∈ M.active ω, ‖M.marks k ω‖) ≤ K)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H)
    (B : ℝ) (hB : 0 ≤ B) (hHB : ∀ p, ‖H p‖ ≤ B) :
    Integrable (finiteJumpGain M.active M.times M.marks H T) P ∧
      (∫ ω, finiteJumpGain M.active M.times M.marks H T ω ∂P) = 0 := by
  classical
  let e := stdOrthonormalBasis ℝ V
  let h := fun i p => inner ℝ (e i) (H p)
  let G := fun i p => h i p • e i
  have hhm : ∀ i, Measurable[𝓕.predictable] (h i) := fun i =>
    continuous_inner.measurable.comp (measurable_const.prodMk hH)
  have hhb : ∀ i p, |h i p| ≤ B := by
    intro i p
    have he : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
    exact (abs_real_inner_le_norm (e i) (H p)).trans (by rw [he, one_mul]; exact hHB p)
  have hcoord := fun i => M.bounded_variation_coordinate_gain hmart K hvar (e i) (h i) (hhm i) B hB (hhb i)
  have hdecomp : H = ∑ i, G i := by
    funext p
    simpa only [Finset.sum_apply] using (e.sum_repr' (H p)).symm
  have heq : finiteJumpGain M.active M.times M.marks H T =
      fun ω => ∑ i, finiteJumpGain M.active M.times M.marks (G i) T ω := by
    funext ω
    rw [hdecomp, finite_gain_finset_sum]
  rw [heq]
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hcoord i).1)
  · rw [integral_finsetSum _ (fun i _ => (hcoord i).1)]
    exact Finset.sum_eq_zero (fun i _ => (hcoord i).2)

#print axioms finite_gain_finset_sum
#print axioms PriceJumpModel.bounded_variation_gain
end FTDAP
