import PredictableAtoms
import Pathwise

open MeasureTheory Set Filter
open scoped RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω ι V : Type*} [LinearOrder ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The finite Stieltjes gain in an explicit enumeration of the path's jumps. -/
noncomputable def finiteJumpGain (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (t : ι) (ω : Ω) : ℝ :=
  ∑ k ∈ jumps ω, if τ k ω ≤ t then ⟪H (τ k ω, ω), Δ k ω⟫ else 0

/-- Continue only after s and only on the event A known at s. -/
noncomputable def continuedStrategy (H : ι × Ω → V) (s : ι) (A : Set Ω)
    (p : ι × Ω) : V := if s < p.1 ∧ p.2 ∈ A then H p else 0

theorem continued_gain_before (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (s t : ι) (A : Set Ω)
    (hts : t ≤ s) (ω : Ω) :
    finiteJumpGain jumps τ Δ (continuedStrategy H s A) t ω = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkt : τ k ω ≤ t
  · have hk : ¬ s < τ k ω := not_lt_of_ge (hkt.trans hts)
    simp [continuedStrategy, hkt, hk]
  · simp [hkt]

theorem continued_gain_after (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (s t : ι) (A : Set Ω)
    (hst : s ≤ t) (ω : Ω) :
    finiteJumpGain jumps τ Δ (continuedStrategy H s A) t ω =
      if ω ∈ A then finiteJumpGain jumps τ Δ H t ω - finiteJumpGain jumps τ Δ H s ω
      else 0 := by
  classical
  by_cases hA : ω ∈ A
  · simp only [hA, ite_true, finiteJumpGain, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hks : τ k ω ≤ s
    · have hkt := hks.trans hst
      simp [continuedStrategy, hA, hks, hkt, not_lt_of_ge hks]
    · have hsk := lt_of_not_ge hks
      by_cases hkt : τ k ω ≤ t <;> simp [continuedStrategy, hA, hks, hsk, hkt]
  · simp [finiteJumpGain, continuedStrategy, hA]

section Measurability
variable [MeasurableSpace Ω] [OrderBot ι] [MeasurableSpace V] [BorelSpace V]

theorem continued_strategy_predictable (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H)
    (s : ι) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    Measurable[𝓕.predictable] (continuedStrategy H s A) := by
  classical
  have hm : MeasurableSet[𝓕.predictable] {p : ι × Ω | s < p.1 ∧ p.2 ∈ A} :=
    measurableSet_predictable_Ioi_prod hA
  exact hH.piecewise hm (measurable_const (a := (0 : V)))

/-- Absence of nonzero nonnegative admissible terminal gains, with the gain
and predictability interpreted explicitly, rather than as an assumed implication. -/
def GainNoArbitrage (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι) : Prop :=
  ∀ H : ι × Ω → V, Measurable[𝓕.predictable] H →
    (∃ b : ℝ, 0 < b ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, -b ≤ finiteJumpGain jumps τ Δ H t ω) →
    (∀ᵐ ω ∂P, 0 ≤ finiteJumpGain jumps τ Δ H T ω) →
    finiteJumpGain jumps τ Δ H T =ᵐ[P] 0

/-- The continuation argument upgrades a terminal lower bound to the same
lower bound at every fixed time. Closure under continuation is proved above. -/
theorem continuation_lower_bound (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, -b ≤ finiteJumpGain jumps τ Δ H t ω)
    (hterminal : ∀ᵐ ω ∂P, -a ≤ finiteJumpGain jumps τ Δ H T ω)
    (s : ι) (hsT : s ≤ T)
    (hsmeas : Measurable[𝓕 s] (finiteJumpGain jumps τ Δ H s)) :
    ∀ᵐ ω ∂P, -a ≤ finiteJumpGain jumps τ Δ H s ω := by
  classical
  let X := finiteJumpGain jumps τ Δ H
  let A : Set Ω := {ω | X s ω < -a}
  have hA : MeasurableSet[𝓕 s] A := hsmeas measurableSet_Iio
  let G := continuedStrategy H s A
  have hG := continued_strategy_predictable 𝓕 H hH s A hA
  have hGb : ∀ᵐ ω ∂P, ∀ t ≤ T, -b ≤ finiteJumpGain jumps τ Δ G t ω := by
    filter_upwards [hbound] with ω hω t ht
    rcases le_total t s with hts | hst
    · rw [continued_gain_before jumps τ Δ H s t A hts ω]
      linarith
    · rw [continued_gain_after jumps τ Δ H s t A hst ω]
      split_ifs with hωA
      · have hx : X s ω < -a := hωA
        have hbω := hω t ht
        change -b ≤ X t ω - X s ω
        change -b ≤ X t ω at hbω
        linarith
      · linarith
  have hGT : ∀ᵐ ω ∂P, 0 ≤ finiteJumpGain jumps τ Δ G T ω := by
    filter_upwards [hterminal] with ω hω
    rw [continued_gain_after jumps τ Δ H s T A hsT ω]
    split_ifs with hωA
    · have hx : X s ω < -a := hωA
      change 0 ≤ X T ω - X s ω
      change -a ≤ X T ω at hω
      linarith
    · exact le_rfl
  have hz := hna G hG ⟨b, hb, hGb⟩ hGT
  filter_upwards [hz, hterminal] with ω hω ht
  by_contra hn
  have hx : ω ∈ A := lt_of_not_ge hn
  rw [continued_gain_after jumps τ Δ H s T A hsT ω, ite_eq_left hx] at hω
  have hx' : X s ω < -a := hx
  change X T ω - X s ω = 0 at hω
  change -a ≤ X T ω at ht
  linarith

end Measurability
#print axioms continuation_lower_bound
end FTDAP
