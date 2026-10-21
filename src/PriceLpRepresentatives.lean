import PriceHilbertReduction

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [SecondCountableTopology V] in
/-- Equality in the common predictable measure preserves every gain value on
one common probability-one set. -/
theorem PriceJumpModel.gain_eq_of_energy_ae
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (G H : NNReal × Ω → V) (he : G =ᵐ[M.energyMeasure c] H) :
    ∀ᵐ ω ∂P, ∀ t, finiteJumpGain M.active M.times M.marks G t ω =
      finiteJumpGain M.active M.times M.marks H t ω := by
  classical
  have ha := M.energyMeasure_ae_at_jumps c hcm hc (fun p => G p = H p) he
  filter_upwards [ha] with ω hω
  intro t
  apply Finset.sum_congr rfl
  intro k hk
  change (if M.times k ω ≤ t then inner ℝ (G (M.times k ω, ω)) (M.marks k ω) else 0) = _
  rw [hω k hk]
  rfl

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Actual gains are constant after the model horizon. -/
theorem PriceJumpModel.gain_clamped_horizon
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (H : NNReal × Ω → V) (t : NNReal) (ω : Ω) :
    finiteJumpGain M.active M.times M.marks H t ω =
      finiteJumpGain M.active M.times M.marks H (min t T) ω := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have ht := (M.bounds ω k hk).2.1
  simp only [le_min_iff, and_iff_left ht]
  rfl

/-- Unit reduction scales to a common Hilbert ball for every positive
admissibility constant. The returned object is an actual predictable L2 class. -/
theorem PriceJumpModel.lp_representative_from_unit_reduction
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (hreduction : ∀ (H : NNReal × Ω → V), Measurable[𝓕.predictable] H →
      (∀ᵐ ω ∂P, ∀ t ≤ T, -1 ≤ finiteJumpGain M.active M.times M.marks H t ω) →
      ∃ G : NNReal × Ω → V, Measurable[𝓕.predictable] G ∧
        (∀ᵐ ω ∂P, ∀ t, finiteJumpGain M.active M.times M.marks G t ω =
          finiteJumpGain M.active M.times M.marks H t ω) ∧
        ∃ hL : MemLp G 2 (M.energyMeasure c), ‖hL.toLp G‖ ≤ 1)
    (H : NNReal × Ω → V) (hH : Measurable[𝓕.predictable] H)
    (a : ℝ) (ha : 0 < a)
    (hadm : ∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain M.active M.times M.marks H t ω) :
    ∃ Y : Lp V 2 (M.energyMeasure c), ‖Y‖ ≤ a ∧
      ∀ᵐ ω ∂P, ∀ t, finiteJumpGain M.active M.times M.marks Y t ω =
        finiteJumpGain M.active M.times M.marks H t ω := by
  have hnormed : ∀ᵐ ω ∂P, ∀ t ≤ T,
      -1 ≤ finiteJumpGain M.active M.times M.marks (a⁻¹ • H) t ω := by
    filter_upwards [hadm] with ω hω
    intro t ht
    rw [finite_gain_smul]
    have hh := mul_le_mul_of_nonneg_left (hω t ht) (inv_pos.mpr ha).le
    have hi : a⁻¹ * (-a) = -1 := by field_simp
    rwa [hi] at hh
  obtain ⟨G, _hG, he, hL, hnorm⟩ := hreduction (a⁻¹ • H) (hH.const_smul _) hnormed
  let Y : Lp V 2 (M.energyMeasure c) := a • hL.toLp G
  have hY : Y =ᵐ[M.energyMeasure c] (a • G : NNReal × Ω → V) := by
    filter_upwards [Lp.coeFn_smul a (hL.toLp G), hL.coeFn_toLp] with p hp hg
    change Y p = a • G p
    rw [hp]
    change a • (hL.toLp G) p = a • G p
    rw [hg]
  refine ⟨Y, ?_, ?_⟩
  · change ‖a • hL.toLp G‖ ≤ a
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith
  · have hYe := M.gain_eq_of_energy_ae c hcm hc Y (a • G) hY
    filter_upwards [hYe, he] with ω hω hGω
    intro t
    rw [hω t, finite_gain_smul, hGω t, finite_gain_smul]
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

#print axioms PriceJumpModel.gain_eq_of_energy_ae
#print axioms PriceJumpModel.gain_clamped_horizon
#print axioms PriceJumpModel.lp_representative_from_unit_reduction
end FTDAP
