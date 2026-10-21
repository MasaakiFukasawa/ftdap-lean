import Continuation

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω ι V : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def preJumpGain (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (t : ι) (ω : Ω) : ℝ :=
  ∑ k ∈ jumps ω, if τ k ω < t then ⟪H (τ k ω, ω), Δ k ω⟫ else 0

theorem left_limit_step (u t : ι) (v : ℝ) :
    Tendsto (fun s => if u ≤ s then v else 0) (𝓝[<] t)
      (𝓝 (if u < t then v else 0)) := by
  by_cases hut : u < t
  · have he₀ : ∀ᶠ s in 𝓝[<] t, u < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hut)
    rw [ite_eq_left hut]
    apply (tendsto_const_nhds (x := v)).congr'
    exact he₀.mono (fun s hs => (ite_eq_left hs.le).symm)
  · have htu : t ≤ u := le_of_not_gt hut
    have he₀ : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
    rw [ite_eq_right hut]
    apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
    exact he₀.mono (fun s hs => (ite_eq_right (not_le_of_gt (hs.trans_le htu))).symm)

theorem finite_gain_left_limit (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (t : ι) (ω : Ω) :
    Tendsto (fun s => finiteJumpGain jumps τ Δ H s ω) (𝓝[<] t)
      (𝓝 (preJumpGain jumps τ Δ H t ω)) := by
  exact tendsto_finsetSum (jumps ω) (fun k _ =>
    left_limit_step (τ k ω) t ⟪H (τ k ω, ω), Δ k ω⟫)

/-- The admissible lower bound also holds just before each positive jump time. -/
theorem pre_jump_gain_lower_bound (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (t T : ι) (ω : Ω)
    [NeBot (𝓝[<] t)] (a : ℝ) (htT : t ≤ T)
    (hbound : ∀ s ≤ T, -a ≤ finiteJumpGain jumps τ Δ H s ω) :
    -a ≤ preJumpGain jumps τ Δ H t ω := by
  apply ge_of_tendsto (finite_gain_left_limit jumps τ Δ H t ω)
  have he : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
  exact he.mono (fun s hs => hbound s (hs.le.trans htT))

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- At a uniquely enumerated jump, the gain equals pre-jump gain plus its increment. -/
theorem gain_at_unique_jump (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (ω : Ω) (k : ℕ)
    (hk : k ∈ jumps ω)
    (hinj : Set.InjOn (fun j => τ j ω) (jumps ω)) :
    finiteJumpGain jumps τ Δ H (τ k ω) ω = preJumpGain jumps τ Δ H (τ k ω) ω +
      ⟪H (τ k ω, ω), Δ k ω⟫ := by
  have he : ∀ j ∈ jumps ω,
      (if τ j ω ≤ τ k ω then ⟪H (τ j ω, ω), Δ j ω⟫ else 0) =
      (if τ j ω < τ k ω then ⟪H (τ j ω, ω), Δ j ω⟫ else 0) +
        (if j = k then ⟪H (τ k ω, ω), Δ k ω⟫ else 0) := by
    intro j hj
    by_cases hjk : j = k
    · subst j
      simp
    · have hne : τ j ω ≠ τ k ω := fun h => hjk (hinj hj hk h)
      by_cases hlt : τ j ω < τ k ω
      · simp [hlt, hlt.le, hjk]
      · have hgt : τ k ω < τ j ω := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [hlt, not_le_of_gt hgt, hjk]
  unfold finiteJumpGain preJumpGain
  simp_rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  simp [hk]

omit [TopologicalSpace ι] [OrderTopology ι] in
/-- Admissibility gives the finite-face compatibility inequality at each jump. -/
theorem jump_wealth_compatibility (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (ω : Ω) (k : ℕ)
    (hk : k ∈ jumps ω) (hinj : Set.InjOn (fun j => τ j ω) (jumps ω))
    (a : ℝ) (hbound : -a ≤ finiteJumpGain jumps τ Δ H (τ k ω) ω) :
    -(a + preJumpGain jumps τ Δ H (τ k ω) ω) ≤ ⟪H (τ k ω, ω), Δ k ω⟫ := by
  rw [gain_at_unique_jump jumps τ Δ H ω k hk hinj] at hbound
  linarith

#print axioms left_limit_step
#print axioms finite_gain_left_limit
#print axioms pre_jump_gain_lower_bound
#print axioms gain_at_unique_jump
#print axioms jump_wealth_compatibility
end FTDAP
