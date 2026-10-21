import WeakDualSlicePreparation
import Mathlib.Analysis.Normed.Operator.NNNorm

open NormedSpace Set Filter
open scoped Topology
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A functional with norm above a positive threshold is detected by a small
predual vector, with the sign chosen to give a positive evaluation. -/
theorem small_vector_detects_dual_norm (f : StrongDual ℝ E) (a : ℝ)
    (ha : 0 < a) (hf : a < ‖f‖) :
    ∃ v : E, ‖v‖ ≤ 1 / a ∧ 1 < f v := by
  obtain ⟨z, hz, hfz⟩ := f.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm
    (r := ⟨a, ha.le⟩) (by exact_mod_cast hf)
  have hz' : ‖z‖ = 1 := by
    simpa only [coe_nnnorm, NNReal.coe_one] using congrArg (fun r : NNReal => (r : ℝ)) hz
  have hfz' : a < |f z| := by exact_mod_cast hfz
  by_cases hpos : 0 ≤ f z
  · refine ⟨a⁻¹ • z, ?_, ?_⟩
    · simp [norm_smul, hz', abs_of_pos ha, one_div]
    · rw [map_smul, smul_eq_mul]
      rw [abs_of_nonneg hpos] at hfz'
      calc
        1 = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
        _ < a⁻¹ * f z := mul_lt_mul_of_pos_left hfz' (inv_pos.mpr ha)
  · refine ⟨a⁻¹ • (-z), ?_, ?_⟩
    · simp [norm_smul, hz', abs_of_pos ha, one_div]
    · rw [map_smul, map_neg, smul_eq_mul]
      rw [abs_of_neg (lt_of_not_ge hpos)] at hfz'
      calc
        1 = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
        _ < a⁻¹ * -f z := mul_lt_mul_of_pos_left hfz' (inv_pos.mpr ha)

/-- Weak-star compact sets lying outside a norm ball have finitely many
small predual vectors that detect every member. -/
theorem compact_dual_finite_detectors (A : Set (WeakDual ℝ E)) (hA : IsCompact A)
    (a : ℝ) (ha : 0 < a) (houtside : ∀ f ∈ A, a < ‖WeakDual.toStrongDual f‖) :
    ∃ S : Finset E, (∀ v ∈ S, ‖v‖ ≤ 1 / a) ∧ ∀ f ∈ A, ∃ v ∈ S, 1 < f v := by
  classical
  let I := {v : E // ‖v‖ ≤ 1 / a}
  let U : I → Set (WeakDual ℝ E) := fun v => {f | 1 < f v.val}
  have hopen : ∀ v, IsOpen (U v) := fun v =>
    isOpen_lt continuous_const (WeakDual.eval_continuous v.val)
  have hcover : A ⊆ ⋃ v : I, U v := by
    intro f hf
    obtain ⟨v, hv, hfv⟩ := small_vector_detects_dual_norm (WeakDual.toStrongDual f) a ha (houtside f hf)
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hfv⟩
  obtain ⟨J, hJ⟩ := hA.elim_finite_subcover U hopen hcover
  refine ⟨J.image Subtype.val, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, _hw, rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  · intro f hf
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hJ hf)
    obtain ⟨hvJ, hvf⟩ := mem_iUnion.mp hv
    exact ⟨v.val, Finset.mem_image.mpr ⟨v, hvJ, rfl⟩, hvf⟩

#print axioms small_vector_detects_dual_norm
#print axioms compact_dual_finite_detectors
end FTDAP
