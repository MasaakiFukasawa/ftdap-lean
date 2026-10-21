import FiniteSelection
import ZeroFaceTrading

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A finite increment set supplies a single constant for every strategy.
Both the auxiliary separator and the reduced portfolio are measurable. -/
theorem measurable_finite_portfolio_reduction (F : Finset V) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (H : α → V) (W : α → ℝ), Measurable H → Measurable W →
    ∃ U G : α → V, Measurable U ∧ Measurable G ∧
      (∀ p, NonnegOn (constraintSet F H W p) (U p)) ∧
      (∀ p, 0 ≤ W p → ‖G p‖ ≤ c * W p) ∧
      ∀ p z, z ∈ zeroFace (constraintSet F H W p) (U p) → ⟪G p, z⟫ = ⟪H p, z⟫ := by
  classical
  choose u hu hmax using (fun J : Finset V => exists_maximal_separator J)
  choose κ hκ hprojection using (fun J : Finset V => portfolio_projection_bound J (u J) (hu J) (hmax J))
  let c : ℝ := 1 + ∑ J ∈ F.powerset, κ J
  have hsum : 0 ≤ ∑ J ∈ F.powerset, κ J :=
    Finset.sum_nonneg (fun J _ => (hκ J).le)
  have hκc : ∀ J ∈ F.powerset, κ J ≤ c := by
    intro J hJ
    have hle := Finset.single_le_sum (fun K (_ : K ∈ F.powerset) => (hκ K).le) hJ
    dsimp [c]
    linarith
  refine ⟨c, by dsimp [c]; linarith, ?_⟩
  intro H W hH hW
  let J : α → Finset V := constraintSet F H W
  have hJF : ∀ p, J p ⊆ F := fun p => Finset.filter_subset _ _
  have hJS : ∀ p, J p ∈ F.powerset := fun p => Finset.mem_powerset.mpr (hJF p)
  have hfiber : ∀ K ∈ F.powerset, MeasurableSet {p | J p = K} :=
    fun K hK => constraint_set_fiber_measurable F H W hH hW K (Finset.mem_powerset.mp hK)
  let proj : Finset V → V →L[ℝ] V :=
    fun K => (Submodule.span ℝ (zeroFace K (u K) : Set V)).starProjection
  let U : α → V := fun p => u (J p)
  let G : α → V := fun p => proj (J p) (H p)
  refine ⟨U, G, measurable_finite_selection F.powerset J hJS hfiber u,
    measurable_finite_projection F.powerset J hJS hfiber proj H hH,
    fun p => hu (J p), ?_, ?_⟩
  · intro p hw
    have hh : ∀ z ∈ zeroFace (J p) (u (J p)), -W p ≤ ⟪H p, z⟫ := by
      intro z hz
      have hzJ := (Finset.mem_filter.mp hz).1
      exact (Finset.mem_filter.mp hzJ).2
    exact (hprojection (J p) (H p) (W p) hw hh).1.trans
      (mul_le_mul_of_nonneg_right (hκc _ (hJS p)) hw)
  · intro p z hz
    have hw : 0 ≤ max 0 (W p) := le_max_left _ _
    have hh : ∀ q ∈ zeroFace (J p) (u (J p)), -max 0 (W p) ≤ ⟪H p, q⟫ := by
      intro q hq
      have hqJ := (Finset.mem_filter.mp hq).1
      have hqW := (Finset.mem_filter.mp hqJ).2
      exact (neg_le_neg (le_max_right 0 (W p))).trans hqW
    exact (hprojection (J p) (H p) (max 0 (W p)) hw hh).2 z hz

#print axioms measurable_finite_portfolio_reduction
end FTDAP

namespace FTDAP
open scoped RealInnerProductSpace
variable {Ω ι V : Type*} [MeasurableSpace Ω] [LinearOrder ι] [OrderBot ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- NA turns the measurable projection into a gain-preserving bounded
portfolio. The constant depends only on the finite increment set. -/
theorem finite_market_portfolio_reduction (P : Measure Ω)
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι) (F : Finset V)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (horizon : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, τ k ω ≤ T)
    (hincrements : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ F) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ (H : ι × Ω → V) (W : ι × Ω → ℝ),
      Measurable[𝓕.predictable] H → Measurable[𝓕.predictable] W →
      (∀ᵐ ω ∂P, ∀ k ∈ jumps ω, 0 ≤ W (τ k ω, ω)) →
      (∀ᵐ ω ∂P, ∀ k ∈ jumps ω, -W (τ k ω, ω) ≤ ⟪H (τ k ω, ω), Δ k ω⟫) →
      ∃ G : ι × Ω → V, Measurable[𝓕.predictable] G ∧
        (∀ᵐ ω ∂P, ∀ t, finiteJumpGain jumps τ Δ G t ω = finiteJumpGain jumps τ Δ H t ω) ∧
        ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, ‖G (τ k ω, ω)‖ ≤ c * W (τ k ω, ω) := by
  let : MeasurableSpace (ι × Ω) := 𝓕.predictable
  obtain ⟨c, hc, hreduce⟩ := measurable_finite_portfolio_reduction (α := ι × Ω) F
  refine ⟨c, hc, ?_⟩
  intro H W hH hW hWpos hconstraint
  obtain ⟨U, G, hU, hG, hnonneg, hnorm, hpreserve⟩ := hreduce H W hH hW
  have hactual : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, Δ k ω ∈ constraintSet F H W (τ k ω, ω) := by
    filter_upwards [hincrements, hconstraint] with ω hω hω' k hk
    exact Finset.mem_filter.mpr ⟨hω k hk, hω' k hk⟩
  have hz := actual_increment_zero_face P 𝓕 jumps τ Δ T hna
    (constraintSet F H W) U hU horizon hactual hnonneg
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hz] with ω hω t
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkt : τ k ω ≤ t
    · simp only [ite_eq_left hkt]
      exact hpreserve (τ k ω, ω) (Δ k ω) (hω k hk)
    · simp [hkt]
  · filter_upwards [hWpos] with ω hω k hk
    exact hnorm (τ k ω, ω) (hω k hk)

#print axioms finite_market_portfolio_reduction
end FTDAP
