import LocalMartingaleFromSeparator
import StateIncrements
import LocalizingIndex

open MeasureTheory Set Filter Function
open scoped Topology
namespace FTDAP
variable {V : Type*} [NormedAddCommGroup V]

/-- A jump covered by a bounded-price localizer has both its value and its left
limit in the same deterministic finite set of price states. -/
theorem stopped_jump_states (f : ℝ → V) (hf : IsCadlag f)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (T σ t b : ℝ) (ht : 0 < t) (htT : t ≤ T) (htσ : t ≤ σ)
    (hstates : ∀ s ∈ Icc 0 T, f s ∈ E)
    (hbound : ∀ s ∈ Icc 0 T, ‖f (min s σ)‖ ≤ b) :
    leftLim f t ∈ E ∧ ‖leftLim f t‖ ≤ b ∧ f t ∈ E ∧ ‖f t‖ ≤ b := by
  have he : ∀ᶠ s in 𝓝[<] t, f s ∈ E ∧ ‖f s‖ ≤ b := by
    have hpos : ∀ᶠ s in 𝓝[<] t, 0 < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)
    filter_upwards [hpos, self_mem_nhdsWithin] with s hs hst
    have hsT : s ∈ Icc 0 T := ⟨hs.le, hst.le.trans htT⟩
    refine ⟨hstates s hsT, ?_⟩
    simpa only [min_eq_left (hst.le.trans htσ)] using hbound s hsT
  obtain ⟨hl, hbl⟩ := finite_state_limit (𝓝[<] t) E hE b f (leftLim f t)
    (tendsto_leftLim_of_tendsto (hf.tendsto_nhdsLT t)) he
  exact ⟨hl, hbl, hstates t ⟨ht.le, htT⟩,
    by simpa only [min_eq_left htσ] using hbound t ⟨ht.le, htT⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Price localizers and local finiteness construct the predictable region
index and deterministic finite increment sets used in portfolio reduction. -/
theorem predictable_stopped_increment_sets
    (P : Measure Ω) (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (T : NNReal)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ m, IsStoppingTime 𝓕 (fun ω => (σ m ω : WithTop NNReal)))
    (hcover : ∀ᵐ ω ∂P, ∃ m, T ≤ σ m ω)
    (b : ℕ → ℝ)
    (hbound : ∀ m, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ m ω) : NNReal) : ℝ) ω‖ ≤ b m) :
    ∃ (index : NNReal × Ω → ℕ) (F : ℕ → Finset V),
      Measurable[𝓕.predictable] index ∧
      ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → t ≤ T →
        S (t : ℝ) ω - leftLim (fun s => S s ω) (t : ℝ) ∈ F (index (t, ω)) := by
  classical
  obtain ⟨F₀, hF₀⟩ := locally_finite_localizing_increments E hE b
  obtain ⟨index, him, hispec⟩ := predictable_localizing_index 𝓕 σ hσ
  let F : ℕ → Finset V := fun n => if n = 0 then ∅ else F₀ (n-1)
  refine ⟨index, F, him, ?_⟩
  have hB : ∀ᵐ ω ∂P, ∀ m, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ m ω) : NNReal) : ℝ) ω‖ ≤ b m := ae_all_iff.mpr hbound
  filter_upwards [hpath, hcover, hB] with ω hω hc hBω
  intro t ht htT
  obtain ⟨m₀, hm₀⟩ := hc
  obtain ⟨m, hm, htσ⟩ := hispec (t, ω) ⟨m₀, htT.trans hm₀⟩
  have hbr : ∀ s ∈ Icc 0 (T : ℝ), ‖S (min s (σ m ω : ℝ)) ω‖ ≤ b m := by
    intro s hs
    have h := hBω m (Real.toNNReal s) (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    simpa only [NNReal.coe_min, Real.coe_toNNReal s hs.1] using h
  obtain ⟨hl, hbl, hr, hbr'⟩ := stopped_jump_states (fun s => S s ω) hω.1 E hE
    (T : ℝ) (σ m ω : ℝ) (t : ℝ) (b m) ht htT htσ hω.2 hbr
  have hf := hF₀ m _ _ hl hr hbl hbr'
  simpa only [F, hm, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] using hf

#print axioms stopped_jump_states
#print axioms predictable_stopped_increment_sets
end FTDAP
