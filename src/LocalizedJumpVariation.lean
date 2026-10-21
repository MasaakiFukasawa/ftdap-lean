import VectorStoppedMartingale
import ModelJumpIdentification
import StoppedStateIncrements

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V]

/-- A bounded-price stop and the index cutoff together bound total jump
variation deterministically; no bound on the original number of jumps is used. -/
theorem PriceJumpModel.localized_jump_variation_bound
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    (S : ℝ → Ω → V) (T : NNReal)
    (M : PriceJumpModel P 𝓕 (fun t => S (t : ℝ)) T)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)
    (κ η : Ω → NNReal) (n : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hηκ : ∀ ω, η ω ≤ κ ω) (hηn : ∀ ω, η ω ≤ M.tailJumpStop n ω)
    (hbound : ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (κ ω) : NNReal) : ℝ) ω‖ ≤ b) :
    ∀ᵐ ω ∂P, (∑ k ∈ (M.active ω).filter (fun k => M.times k ω ≤ η ω),
      ‖M.marks k ω‖) ≤ (n + 1 : ℕ) * (2 * b) := by
  classical
  have hmarks := M.marks_eq_price_jumps S T (hpath.mono (fun _ h => h.1))
  filter_upwards [hpath, hbound, hmarks] with ω hω hB hΔ
  let J := (M.active ω).filter (fun k => M.times k ω ≤ η ω)
  have hcard : J.card ≤ n + 1 := by
    apply le_trans (Finset.card_le_card ?_) (M.tailJumpStop_card_bound n ω)
    intro k hk
    obtain ⟨hk, ht⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hk, ht.trans (hηn ω)⟩
  have hnorm : ∀ k ∈ J, ‖M.marks k ω‖ ≤ 2 * b := by
    intro k hk
    obtain ⟨hk, ht⟩ := Finset.mem_filter.mp hk
    have hbr : ∀ s ∈ Icc 0 (T : ℝ), ‖S (min s (κ ω : ℝ)) ω‖ ≤ b := by
      intro s hs
      have h := hB (Real.toNNReal s) (Real.toNNReal_le_iff_le_coe.mpr hs.2)
      simpa only [NNReal.coe_min, Real.coe_toNNReal s hs.1] using h
    obtain ⟨_hl, hbl, _hr, hbr'⟩ := stopped_jump_states (fun s => S s ω) hω.1 E hE
      (T : ℝ) (κ ω : ℝ) (M.times k ω : ℝ) b (M.bounds ω k hk).1
      (M.bounds ω k hk).2.1 (ht.trans (hηκ ω)) hω.2 hbr
    rw [hΔ k hk]
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    (∑ k ∈ J, ‖M.marks k ω‖) ≤ ∑ _k ∈ J, 2 * b := Finset.sum_le_sum hnorm
    _ = (J.card : ℝ) * (2 * b) := by simp
    _ ≤ (n + 1 : ℕ) * (2 * b) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

#print axioms PriceJumpModel.localized_jump_variation_bound
end FTDAP
