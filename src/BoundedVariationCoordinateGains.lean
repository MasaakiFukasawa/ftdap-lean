import PredictableAtomBalance

open MeasureTheory Set Filter
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

/-- For a martingale with bounded total jump variation, bounded predictable
holdings in any fixed direction have integrable, zero-mean terminal gains.
The extension from rectangles to all predictable holdings uses actual atomic
measure balance, not an assumed integration theorem. -/
theorem PriceJumpModel.bounded_variation_coordinate_gain
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (hmart : Martingale (fun (t : Iic T) => S t.val) (horizonFiltration 𝓕 T) P)
    (K : ℝ) (hvar : ∀ᵐ ω ∂P, (∑ k ∈ M.active ω, ‖M.marks k ω‖) ≤ K)
    (v : V) (h : NNReal × Ω → ℝ) (hh : Measurable[𝓕.predictable] h)
    (B : ℝ) (hB : 0 ≤ B) (hhB : ∀ p, |h p| ≤ B) :
    Integrable (finiteJumpGain M.active M.times M.marks (fun p => h p • v) T) P ∧
      (∫ ω, finiteJumpGain M.active M.times M.marks (fun p => h p • v) T ω ∂P) = 0 := by
  classical
  let atom := fun k ω => (M.times k ω, ω)
  have ha : ∀ k, @Measurable Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable (atom k) := fun k =>
    measurable_predictable_atom 𝓕 (M.times k) (M.stopping k).measurable'.untopA
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  let d := fun k ω => if k ∈ M.active ω then inner ℝ v (M.marks k ω) else 0
  have hd : ∀ k, Measurable (d k) := by
    intro k
    have hmk := (M.measurable_marks k).mono (M.stopping k).measurableSpace_le le_rfl
    exact (continuous_inner.measurable.comp (measurable_const.prodMk hmk)).ite
      ((M.stopping k).measurableSpace_le _ (M.measurable_active k)) measurable_const
  have hs : ∀ ω k, k ∉ M.active ω → d k ω = 0 := fun _ _ hk => ite_eq_right hk
  have hmass : ∀ᵐ ω ∂P, (∑ k ∈ M.active ω, |d k ω|) ≤ ‖v‖ * K := by
    filter_upwards [hvar] with ω hω
    calc
      _ ≤ ∑ k ∈ M.active ω, ‖v‖ * ‖M.marks k ω‖ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [show d k ω = inner ℝ v (M.marks k ω) from ite_eq_left hk]
        exact abs_real_inner_le_norm _ _
      _ = ‖v‖ * ∑ k ∈ M.active ω, ‖M.marks k ω‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ ‖v‖ * K := mul_le_mul_of_nonneg_left hω (norm_nonneg v)
  have hz : ∀ A, MeasurableSet[𝓕 0] A →
      (∫ ω, ∑ k ∈ M.active ω, d k ω * ({(0 : NNReal)} ×ˢ A).indicator (fun _ => (1 : ℝ)) (atom k ω) ∂P) = 0 := by
    intro A _
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall (fun ω => Finset.sum_eq_zero (fun k hk => by
      have hn : atom k ω ∉ {(0 : NNReal)} ×ˢ A := fun hmem =>
        (ne_of_gt (M.bounds ω k hk).1) hmem.1
      simp [hn]))
  have hr : ∀ s A, MeasurableSet[𝓕 s] A →
      (∫ ω, ∑ k ∈ M.active ω, d k ω * (Ioi s ×ˢ A).indicator (fun _ => (1 : ℝ)) (atom k ω) ∂P) = 0 := by
    intro s A hA
    have hpath : ∀ ω, (∑ k ∈ M.active ω, d k ω *
        (Ioi s ×ˢ A).indicator (fun _ => (1 : ℝ)) (atom k ω)) =
        finiteJumpGain M.active M.times M.marks (continuedStrategy (fun _ => v) s A) T ω := by
      intro ω
      apply Finset.sum_congr rfl
      intro k hk
      have ht := (M.bounds ω k hk).2.1
      by_cases hst : s < M.times k ω <;> by_cases hω : ω ∈ A <;>
        simp [d, hk, atom, continuedStrategy, hst, hω, ht]
    simp_rw [hpath]
    by_cases hsT : s ≤ T
    · have he : (fun ω => finiteJumpGain M.active M.times M.marks
          (continuedStrategy (fun _ => v) s A) T ω) =ᵐ[P]
          A.indicator (fun ω => inner ℝ v (S T ω - S s ω)) := by
        filter_upwards [M.constant_gain_representation v] with ω hω
        rw [continued_gain_after M.active M.times M.marks _ s T A hsT, hω T le_rfl, hω s hsT]
        by_cases haω : ω ∈ A <;> simp [haω, inner_sub_right]
      rw [integral_congr_ae he, integral_indicator ((𝓕.le s) A hA)]
      have hi := ((hmart.integrable (⟨T, Set.mem_Iic.mpr (le_refl T)⟩ : Iic T)).sub
        (hmart.integrable (⟨s, hsT⟩ : Iic T))).integrableOn (s := A)
      have hi' : IntegrableOn (fun ω => S T ω - S s ω) A P := hi
      rw [integral_inner hi' v]
      have hset : (∫ ω in A, S T ω - S s ω ∂P) = 0 := by
        rw [integral_sub (hmart.integrable (⟨T, Set.mem_Iic.mpr (le_refl T)⟩ : Iic T)).integrableOn
          (hmart.integrable (⟨s, hsT⟩ : Iic T)).integrableOn]
        have hEq := hmart.setIntegral_eq (i := (⟨s, hsT⟩ : Iic T))
          (j := (⟨T, Set.mem_Iic.mpr (le_refl T)⟩ : Iic T)) hsT hA
        exact sub_eq_zero.mpr hEq.symm
      rw [hset, inner_zero_right]
    · have he : ∀ ω, finiteJumpGain M.active M.times M.marks
          (continuedStrategy (fun _ => v) s A) T ω = 0 := fun ω =>
        continued_gain_before M.active M.times M.marks _ s T A (le_of_not_ge hsT) ω
      simp_rw [he]
      exact integral_zero _ _
  have hbalance := predictable_atom_measure_balance P 𝓕 atom ha d hd M.active hs (‖v‖*K) hmass hz hr
  have hzero := bounded_signed_atomic_sum_zero_of_balance P atom ha d hd M.active hs (‖v‖*K)
    hmass hbalance h hh B hB hhB
  have hint := bounded_signed_atomic_sum_integrable P atom ha d hd M.active hs (‖v‖*K) hmass h hh B hB hhB
  have hgain : (fun ω => ∑ k ∈ M.active ω, d k ω * h (atom k ω)) =
      finiteJumpGain M.active M.times M.marks (fun p => h p • v) T := by
    funext ω
    apply Finset.sum_congr rfl
    intro k hk
    simp [d, hk, atom, (M.bounds ω k hk).2.1, real_inner_smul_left, mul_comm]
  rw [hgain] at hint hzero
  exact ⟨hint, hzero⟩

#print axioms PriceJumpModel.bounded_variation_coordinate_gain
end FTDAP
