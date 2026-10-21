import L1DualBound

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every real L1 functional on a probability space is integration against
an essentially bounded function, with the expected operator-norm bound. -/
theorem l1_dual_representation (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 1 P →L[ℝ] ℝ) :
    ∃ f : Lp ℝ ∞ P, ‖f‖ ≤ ‖L‖ ∧ ∀ z : Lp ℝ 1 P, L z = claimsPairing P f z := by
  obtain ⟨Y, hY⟩ := l1_functional_L2_representation P L
  have hbound := l1_hilbert_representative_abs_bound P L Y hY
  have hmem : MemLp (fun ω => Y ω) ∞ P := MemLp.of_bound
    Y.val.stronglyMeasurable.aestronglyMeasurable ‖L‖ (by simpa only [Real.norm_eq_abs] using hbound)
  let f := hmem.toLp (fun ω => Y ω)
  have hf : f =ᵐ[P] Y := hmem.coeFn_toLp
  have hfnorm : ‖f‖ ≤ ‖L‖ := by
    have hb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ ‖L‖ := by
      filter_upwards [hf, hbound] with ω hω hbω
      rw [hω, Real.norm_eq_abs]
      exact hbω
    simpa using Lp.norm_le_of_ae_bound (norm_nonneg L) hb
  have hpair : ∀ g : Lp ℝ 2 P, claimsPairing P f (l2ToL1 P g) = ⟪Y, g⟫ := by
    intro g
    rw [claimsPairing_eq_integral, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with ω hω
    rw [hω]
    simp [mul_comm]
  let R := claimsPairingCLM P f
  have hclosed : IsClosed {z : Lp ℝ 1 P | L z = R z} := isClosed_eq L.continuous R.continuous
  have hrange : range (l2ToL1 P) ⊆ {z : Lp ℝ 1 P | L z = R z} := by
    rintro z ⟨g, rfl⟩
    exact (hY g).trans (hpair g).symm
  refine ⟨f, hfnorm, ?_⟩
  intro z
  exact (closure_minimal hrange hclosed) (l2ToL1_dense P z)

#print axioms l1_dual_representation
end FTDAP
