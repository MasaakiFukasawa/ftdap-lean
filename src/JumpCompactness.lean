import ConvexTail
import JumpMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace FTDAP
variable {Ω α H : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Bounded reduced portfolios have forward convex averages converging simultaneously
at every atom with positive weight, on a single full-probability sample set. -/
theorem komlos_jump_atoms (P : Measure Ω) (atom : ℕ → Ω → α)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (f : ℕ → Lp H 2 (jumpMeasure P atom weight)) (R : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ R) :
    ∃ (g : ℕ → Lp H 2 (jumpMeasure P atom weight))
      (Y : Lp H 2 (jumpMeasure P atom weight)),
      (∀ n, g n ∈ convexHull ℝ (f '' Ici n)) ∧
      ∀ᵐ ω ∂P, ∀ k, weight k ω ≠ 0 →
        Tendsto (fun n => g n (atom k ω)) atTop (𝓝 (Y (atom k ω))) := by
  obtain ⟨g₀, Y, hg₀, hlim⟩ := komlos_L2 f R hf
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  refine ⟨g₀ ∘ φ, Y, ?_, ?_⟩
  · intro n
    apply convexHull_mono (Set.image_mono (Ici_subset_Ici.mpr (hφ.id_le n)))
    exact hg₀ (φ n)
  · exact ae_at_jump_atoms P atom weight ha hw
      (fun x => Tendsto (fun n => g₀ (φ n) x) atTop (𝓝 (Y x))) hae

#print axioms komlos_jump_atoms
end FTDAP
