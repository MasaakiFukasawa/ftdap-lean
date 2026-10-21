import SourceClaimSlices
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Inclusion of L2 into L1 on a probability space, using the same AE class. -/
noncomputable def l2ToL1 (P : Measure Ω) [IsProbabilityMeasure P] : Lp ℝ 2 P →L[ℝ] Lp ℝ 1 P := by
  let I : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 1 P := {
    toFun := fun f => ⟨f.val, (Lp.memLp f).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  apply I.mkContinuous 1
  intro f
  rw [one_mul, Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

@[simp]
theorem l2ToL1_coe (P : Measure Ω) [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    (l2ToL1 P f : Ω → ℝ) = f := rfl

/-- The L2 inclusion has dense range in L1 because it contains all simple functions. -/
theorem l2ToL1_dense (P : Measure Ω) [IsProbabilityMeasure P] : DenseRange (l2ToL1 P) := by
  apply (Lp.simpleFunc.dense (E := ℝ) (μ := P) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).mono
  intro f hf
  let s : Lp.simpleFunc ℝ 1 P := ⟨f, hf⟩
  let φ := Lp.simpleFunc.toSimpleFunc s
  have hφ : MemLp φ 2 P := φ.memLp_of_isFiniteMeasure 2 P
  refine ⟨hφ.toLp φ, ?_⟩
  apply Lp.ext
  have he := Lp.simpleFunc.toSimpleFunc_eq_toFun s
  filter_upwards [hφ.coeFn_toLp, he] with ω hω hsω
  change (hφ.toLp φ) ω = f ω
  exact hω.trans hsω

/-- Restricting an L1 functional to L2 gives a Hilbert representative. -/
theorem l1_functional_L2_representation (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 1 P →L[ℝ] ℝ) :
    ∃ Y : Lp ℝ 2 P, ∀ g : Lp ℝ 2 P, L (l2ToL1 P g) = ⟪Y, g⟫ := by
  let Y := (InnerProductSpace.toDual ℝ (Lp ℝ 2 P)).symm (L.comp (l2ToL1 P))
  refine ⟨Y, ?_⟩
  intro g
  change (L.comp (l2ToL1 P)) g =
    inner ℝ ((InnerProductSpace.toDual ℝ (Lp ℝ 2 P)).symm (L.comp (l2ToL1 P))) g
  symm
  exact InnerProductSpace.toDual_symm_apply

#print axioms l2ToL1_coe
#print axioms l2ToL1_dense
#print axioms l1_functional_L2_representation
end FTDAP
