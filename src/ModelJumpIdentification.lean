import StoppedStateIncrements

open MeasureTheory Set Filter Function
open scoped Topology
namespace FTDAP
variable {V : Type*} [NormedAddCommGroup V]
attribute [local instance] Classical.propDecidable

/-- Vector-valued step functions have the expected left limit. -/
theorem vector_step_left_limit (u t : ℝ) (v : V) :
    Tendsto (fun s => if u ≤ s then v else 0) (𝓝[<] t)
      (𝓝 (if u < t then v else 0)) := by
  by_cases hut : u < t
  · have he : ∀ᶠ s in 𝓝[<] t, u < s := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hut)
    rw [ite_eq_left hut]
    exact (tendsto_const_nhds (x := v)).congr'
      (he.mono (fun s hs => (ite_eq_left hs.le).symm))
  · have he : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
    rw [ite_eq_right hut]
    exact (tendsto_const_nhds (x := (0 : V))).congr'
      (he.mono (fun s hs => (ite_eq_right (not_le_of_gt (hs.trans_le (le_of_not_gt hut)))).symm))

/-- At an injectively indexed arrival, the vector sum adds exactly its mark. -/
theorem vector_sum_at_arrival (J : Finset ℕ) (τ : ℕ → ℝ) (Δ : ℕ → V)
    (k : ℕ) (hk : k ∈ J) (hinj : Set.InjOn τ (J : Set ℕ)) :
    (∑ j ∈ J, if τ j ≤ τ k then Δ j else 0) =
      (∑ j ∈ J, if τ j < τ k then Δ j else 0) + Δ k := by
  have he : ∀ j ∈ J, (if τ j ≤ τ k then Δ j else 0) =
      (if τ j < τ k then Δ j else 0) + (if j = k then Δ k else 0) := by
    intro j hj
    by_cases hjk : j = k
    · subst j; simp
    · have hne : τ j ≠ τ k := fun h => hjk (hinj hj hk h)
      by_cases hlt : τ j < τ k
      · simp [hlt, hlt.le, hjk]
      · have hgt : τ k < τ j := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [hlt, not_le_of_gt hgt, hjk]
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  simp [hk]

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

/-- The model's marks are the actual jumps of the original price, almost
surely. This is derived from its representation and distinct positive times. -/
theorem PriceJumpModel.marks_eq_price_jumps
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    (S : ℝ → Ω → V) (T : NNReal)
    (M : PriceJumpModel P 𝓕 (fun t => S (t : ℝ)) T)
    (hcad : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω)) :
    ∀ᵐ ω ∂P, ∀ k ∈ M.active ω, M.marks k ω =
      S (M.times k ω : ℝ) ω - leftLim (fun t => S t ω) (M.times k ω : ℝ) := by
  filter_upwards [M.representation, hcad] with ω hrep hc
  intro k hk
  let t : ℝ := M.times k ω
  let pre : V := ∑ j ∈ M.active ω,
    if (M.times j ω : ℝ) < t then M.marks j ω else 0
  have ht : 0 < t := (M.bounds ω k hk).1
  have htT : t ≤ (T : ℝ) := (M.bounds ω k hk).2.1
  have hleft : Tendsto (fun s => S s ω - S 0 ω) (𝓝[<] t)
      (𝓝 (leftLim (fun s => S s ω) t - S 0 ω)) :=
    (tendsto_leftLim_of_tendsto (hc.tendsto_nhdsLT t)).sub tendsto_const_nhds
  have hsum : Tendsto (fun s => ∑ j ∈ M.active ω,
      if (M.times j ω : ℝ) ≤ s then M.marks j ω else 0) (𝓝[<] t) (𝓝 pre) :=
    tendsto_finsetSum _ (fun j _ => vector_step_left_limit _ t _)
  have he : (fun s => S s ω - S 0 ω) =ᶠ[𝓝[<] t]
      (fun s => ∑ j ∈ M.active ω, if (M.times j ω : ℝ) ≤ s then M.marks j ω else 0) := by
    have hp : ∀ᶠ s in 𝓝[<] t, 0 < s := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)
    filter_upwards [hp, self_mem_nhdsWithin] with s hs hst
    have h := hrep (Real.toNNReal s) (Real.toNNReal_le_iff_le_coe.mpr (hst.le.trans htT))
    simpa only [Real.coe_toNNReal s hs.le, NNReal.coe_zero, ← NNReal.coe_le_coe] using h
  have hl : leftLim (fun s => S s ω) t - S 0 ω = pre :=
    tendsto_nhds_unique hleft (hsum.congr' he.symm)
  have hi : Set.InjOn (fun j => (M.times j ω : ℝ)) (M.active ω : Set ℕ) := by
    intro i hi j hj heq
    exact M.injective_times ω hi hj (NNReal.coe_injective heq)
  have ha := vector_sum_at_arrival (M.active ω) (fun j => (M.times j ω : ℝ))
    (fun j => M.marks j ω) k hk hi
  have hv : S t ω - S 0 ω = pre + M.marks k ω := by
    have hr := hrep (M.times k ω) (M.bounds ω k hk).2.1
    simpa only [← NNReal.coe_le_coe, NNReal.coe_zero] using hr.trans ha
  calc
    M.marks k ω = (pre + M.marks k ω) - pre := by abel
    _ = (S t ω - S 0 ω) - (leftLim (fun s => S s ω) t - S 0 ω) := by rw [hv, hl]
    _ = S t ω - leftLim (fun s => S s ω) t := by abel

#print axioms vector_step_left_limit
#print axioms vector_sum_at_arrival
#print axioms PriceJumpModel.marks_eq_price_jumps
end FTDAP
