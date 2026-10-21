import SourceWeightedMeasure

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Finite Gronwall estimate on arbitrarily indexed, distinctly timed jumps.
It uses the actual pre-jump gain and needs no supplied ordered enumeration. -/
theorem finite_gain_variation_product (J : Finset ℕ) (τ : ℕ → NNReal)
    (Δ H : ℕ → V) (c : ℕ → ℝ) (hc : ∀ k, 1 ≤ c k)
    (hinj : Set.InjOn τ (J : Set ℕ))
    (hG : ∀ k ∈ J, ‖H k‖ ≤ c k *
      (1 + ∑ j ∈ J, if τ j < τ k then inner ℝ (H j) (Δ j) else 0)) :
    (∑ k ∈ J, |inner ℝ (H k) (Δ k)|) ≤
      (∏ k ∈ J, (1 + c k * ‖Δ k‖)) - 1 := by
  revert hinj hG
  induction J using Finset.strongInductionOn with
  | _ J ih =>
    intro hinj hG
    by_cases hJ : J.Nonempty
    · obtain ⟨k, hk, hmax⟩ := J.exists_max_image τ hJ
      have hpre : ∀ j ∈ J.erase k,
          (∑ l ∈ J, if τ l < τ j then inner ℝ (H l) (Δ l) else 0) =
          ∑ l ∈ J.erase k, if τ l < τ j then inner ℝ (H l) (Δ l) else 0 := by
        intro j hj
        rw [← Finset.add_sum_erase J _ hk]
        rw [ite_eq_right (not_lt_of_ge (hmax j (Finset.mem_of_mem_erase hj))), zero_add]
      have hsmall := ih (J.erase k) (Finset.erase_ssubset hk)
        (hinj.mono (Finset.erase_subset k J)) (fun j hj => by
          simpa only [hpre j hj] using hG j (Finset.mem_of_mem_erase hj))
      have htop : (∑ j ∈ J, if τ j < τ k then inner ℝ (H j) (Δ j) else 0) =
          ∑ j ∈ J.erase k, inner ℝ (H j) (Δ j) := by
        rw [← Finset.add_sum_erase J _ hk, ite_eq_right (lt_irrefl (τ k)), zero_add]
        apply Finset.sum_congr rfl
        intro j hj
        have hjJ := Finset.mem_of_mem_erase hj
        have hne : τ j ≠ τ k := fun he => (Finset.ne_of_mem_erase hj) (hinj hjJ hk he)
        exact ite_eq_left (lt_of_le_of_ne (hmax j hjJ) hne)
      have hsum : (∑ j ∈ J.erase k, inner ℝ (H j) (Δ j)) ≤
          (∏ j ∈ J.erase k, (1 + c j * ‖Δ j‖)) - 1 := by
        apply le_trans _ hsmall
        exact Finset.sum_le_sum (fun j _ => le_abs_self _)
      have hnorm : ‖H k‖ ≤ c k * (∏ j ∈ J.erase k, (1 + c j * ‖Δ j‖)) := by
        have h := hG k hk
        rw [htop] at h
        exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans (hc k)))
      have hgain := (abs_real_inner_le_norm (H k) (Δ k)).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg (Δ k)))
      rw [← Finset.add_sum_erase J _ hk, ← Finset.mul_prod_erase J _ hk]
      nlinarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hJ]
      simp

/-- The pre-jump norm constraint gives the common terminal product envelope. -/
theorem finite_portfolio_product_envelope (J : Finset ℕ) (τ : ℕ → NNReal)
    (Δ H : ℕ → V) (c : ℕ → ℝ) (hc : ∀ k, 1 ≤ c k)
    (hinj : Set.InjOn τ (J : Set ℕ))
    (hG : ∀ k ∈ J, ‖H k‖ ≤ c k *
      (1 + ∑ j ∈ J, if τ j < τ k then inner ℝ (H j) (Δ j) else 0)) :
    ∀ k ∈ J, ‖H k‖ ≤ c k * (∏ j ∈ J, (1 + c j * ‖Δ j‖)) := by
  intro k hk
  let K := J.filter (fun j => τ j < τ k)
  have hK : K ⊆ J := Finset.filter_subset _ _
  have hpre : ∀ j ∈ K,
      (∑ l ∈ J, if τ l < τ j then inner ℝ (H l) (Δ l) else 0) =
      ∑ l ∈ K, if τ l < τ j then inner ℝ (H l) (Δ l) else 0 := by
    intro j hj
    symm
    apply Finset.sum_subset hK
    intro l hl hn
    apply ite_eq_right
    intro hlt
    exact hn (Finset.mem_filter.mpr ⟨hl, hlt.trans (Finset.mem_filter.mp hj).2⟩)
  have hvar := finite_gain_variation_product K τ Δ H c hc (hinj.mono hK)
    (fun j hj => by simpa only [hpre j hj] using hG j (hK hj))
  have hsum : (∑ j ∈ K, inner ℝ (H j) (Δ j)) ≤
      (∏ j ∈ K, (1 + c j * ‖Δ j‖)) - 1 :=
    (Finset.sum_le_sum (fun j _ => le_abs_self _)).trans hvar
  have hprod : (∏ j ∈ K, (1 + c j * ‖Δ j‖)) ≤
      ∏ j ∈ J, (1 + c j * ‖Δ j‖) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hK
    · intro j _
      have hcj : 0 ≤ c j := zero_le_one.trans (hc j)
      positivity
    · intro j _ _
      exact le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans (hc j)) (norm_nonneg _))
  have he : (∑ j ∈ J, if τ j < τ k then inner ℝ (H j) (Δ j) else 0) =
      ∑ j ∈ K, inner ℝ (H j) (Δ j) := by
    simp only [K, Finset.sum_filter]
  have hnorm := hG k hk
  rw [he] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans (hc k)))

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V]

/-- The actual predictable pre-wealth bound yields unit L2 norm in the
constructed common measure, without any supplied terminal envelope bound. -/
theorem PriceJumpModel.energy_of_pre_wealth_bound
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (G : NNReal × Ω → V) (hG : Measurable[𝓕.predictable] G)
    (hbound : ∀ᵐ ω ∂P, ∀ k ∈ M.active ω,
      ‖G (M.times k ω, ω)‖ ≤ c (M.times k ω, ω) *
        (1 + preJumpGain M.active M.times M.marks G (M.times k ω) ω)) :
    ∃ hL : MemLp G 2 (M.energyMeasure c), ‖hL.toLp G‖ ≤ 1 := by
  apply M.energy_memLp c hcm hc G hG
  filter_upwards [hbound] with ω hω
  exact finite_portfolio_product_envelope (M.active ω) (fun k => M.times k ω)
    (fun k => M.marks k ω) (fun k => G (M.times k ω, ω)) (fun k => c (M.times k ω, ω))
    (fun k => hc _) (M.injective_times ω) hω

#print axioms finite_portfolio_product_envelope
#print axioms PriceJumpModel.energy_of_pre_wealth_bound
#print axioms finite_gain_variation_product
end FTDAP
