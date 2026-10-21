import TradingCone

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω ι V : Type*} [MeasurableSpace Ω] [LinearOrder ι] [OrderBot ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- Under NA, a predictable strategy with nonnegative increments has zero
pairing at each actual jump on one full-measure set. -/
theorem nonnegative_jump_gains_vanish (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (U : ι × Ω → V) (hU : Measurable[𝓕.predictable] U)
    (horizon : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, τ k ω ≤ T)
    (hinc : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, 0 ≤ ⟪U (τ k ω, ω), Δ k ω⟫) :
    ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, ⟪U (τ k ω, ω), Δ k ω⟫ = 0 := by
  have hnonneg : ∀ᵐ ω ∂P, ∀ t, 0 ≤ finiteJumpGain jumps τ Δ U t ω := by
    filter_upwards [hinc] with ω hω t
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact hω k hk
    · exact le_rfl
  have hbound : ∃ b : ℝ, 0 < b ∧ ∀ᵐ ω ∂P, ∀ t ≤ T,
      -b ≤ finiteJumpGain jumps τ Δ U t ω := by
    refine ⟨1, zero_lt_one, hnonneg.mono ?_⟩
    intro ω hω t _
    linarith [hω t]
  have hz := hna U hU hbound (hnonneg.mono (fun _ h => h T))
  filter_upwards [hinc, horizon, hz] with ω hi ht hzero k hk
  have hsum : finiteJumpGain jumps τ Δ U T ω =
      ∑ j ∈ jumps ω, ⟪U (τ j ω, ω), Δ j ω⟫ := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [ht j hj]
  have hle : ⟪U (τ k ω, ω), Δ k ω⟫ ≤ ∑ j ∈ jumps ω, ⟪U (τ j ω, ω), Δ j ω⟫ :=
    Finset.single_le_sum (fun j hj => hi j hj) hk
  rw [← hsum, hzero] at hle
  exact le_antisymm hle (hi k hk)

/-- The stochastic NA step that forces every actual increment into the zero
face chosen by the finite-dimensional geometry. -/
theorem actual_increment_zero_face (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (J : ι × Ω → Finset V) (U : ι × Ω → V) (hU : Measurable[𝓕.predictable] U)
    (horizon : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, τ k ω ≤ T)
    (hJ : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ J (τ k ω, ω))
    (hsep : ∀ p, NonnegOn (J p) (U p)) :
    ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ zeroFace (J (τ k ω, ω)) (U (τ k ω, ω)) := by
  have hinc : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, 0 ≤ ⟪U (τ k ω, ω), Δ k ω⟫ :=
    hJ.mono (fun ω hω k hk => hsep _ _ (hω k hk))
  have hz := nonnegative_jump_gains_vanish P 𝓕 jumps τ Δ T hna U hU horizon hinc
  filter_upwards [hJ, hz] with ω hj hzero k hk
  exact Finset.mem_filter.mpr ⟨hj k hk, hzero k hk⟩

#print axioms nonnegative_jump_gains_vanish
#print axioms actual_increment_zero_face
end FTDAP
