import TradingGains
import CadlagBase

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω ι V : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem right_continuous_step (u : ι) (v : ℝ) :
    IsRightContinuous (fun t => if u ≤ t then v else 0) := by
  intro t
  by_cases hut : u ≤ t
  · have he₀ : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
    have he : ∀ᶠ s in 𝓝[>] t, u ≤ s := he₀.mono (fun _ h => hut.trans h.le)
    change Tendsto (fun s => if u ≤ s then v else 0) (𝓝[>] t) (𝓝 (if u ≤ t then v else 0))
    rw [ite_eq_left hut]
    apply (tendsto_const_nhds (x := v)).congr'
    exact he.mono (fun _ h => (ite_eq_left h).symm)
  · have ht : t < u := lt_of_not_ge hut
    have he₀ : ∀ᶠ s in 𝓝[>] t, s < u := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
    have he : ∀ᶠ s in 𝓝[>] t, ¬ u ≤ s := he₀.mono (fun _ h => not_le_of_gt h)
    change Tendsto (fun s => if u ≤ s then v else 0) (𝓝[>] t) (𝓝 (if u ≤ t then v else 0))
    rw [ite_eq_right hut]
    apply (tendsto_const_nhds (x := (0 : ℝ))).congr'
    exact he.mono (fun _ h => (ite_eq_right h).symm)

theorem finite_gain_right_continuous (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H : ι × Ω → V) (ω : Ω) :
    IsRightContinuous (fun t => finiteJumpGain jumps τ Δ H t ω) := by
  intro t
  exact tendsto_finsetSum (jumps ω) (fun k _ =>
    (right_continuous_step (τ k ω) ⟪H (τ k ω, ω), Δ k ω⟫ t).tendsto)

/-- Right continuity and a dense set of time tests extend a lower bound to
all times before the horizon; the endpoint is handled explicitly. -/
theorem dense_time_lower_bound [DenselyOrdered ι] (D : Set ι) (hdense : Dense D)
    (f : ι → ℝ) (hf : IsRightContinuous f) (T : ι) (a : ℝ)
    (hD : ∀ t ∈ D, t ≤ T → -a ≤ f t) (hT : -a ≤ f T) :
    ∀ t ≤ T, -a ≤ f t := by
  intro t htT
  rcases htT.eq_or_lt with rfl | hlt
  · exact hT
  · by_contra hn
    have hft : f t < -a := lt_of_not_ge hn
    have hb : {s | f s < -a} ∈ 𝓝[>] t := (hf t) (Iio_mem_nhds hft)
    obtain ⟨u, htu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hlt).mp hb
    obtain ⟨q, hqD, htq, hqu⟩ := hdense.exists_between (lt_min htu hlt)
    have hqT : q ≤ T := (hqu.trans_le (min_le_right u T)).le
    have hbad : f q < -a := hu ⟨htq, hqu.trans_le (min_le_left u T)⟩
    exact (not_lt_of_ge (hD q hqD hqT)) hbad

variable [MeasurableSpace Ω] [OrderBot ι] [MeasurableSpace V] [BorelSpace V]

/-- The complete admissibility upgrade: one exceptional null set for all
times, not a time-dependent collection of exceptional sets. -/
theorem continuation_all_times [DenselyOrdered ι] [SecondCountableTopology ι]
    (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (hna : GainNoArbitrage P 𝓕 jumps τ Δ T)
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, -b ≤ finiteJumpGain jumps τ Δ H t ω)
    (hterminal : ∀ᵐ ω ∂P, -a ≤ finiteJumpGain jumps τ Δ H T ω)
    (hadapt : ∀ s, Measurable[𝓕 s] (finiteJumpGain jumps τ Δ H s)) :
    ∀ᵐ ω ∂P, ∀ t ≤ T, -a ≤ finiteJumpGain jumps τ Δ H t ω := by
  obtain ⟨D, hcount, hdense⟩ := exists_countable_dense ι
  have hD : ∀ᵐ ω ∂P, ∀ t ∈ D, t ≤ T → -a ≤ finiteJumpGain jumps τ Δ H t ω := by
    apply (ae_ball_iff hcount).mpr
    intro t _
    by_cases ht : t ≤ T
    · exact (continuation_lower_bound P 𝓕 jumps τ Δ T hna H hH
        a b ha hb hbound hterminal t ht (hadapt t)).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (ht h).elim)
  filter_upwards [hD, hterminal] with ω hω hT
  exact dense_time_lower_bound D hdense _ (finite_gain_right_continuous jumps τ Δ H ω) T a hω hT

#print axioms continuation_all_times
end FTDAP
