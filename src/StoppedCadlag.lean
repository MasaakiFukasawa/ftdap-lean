import ProgressiveRight
import StochasticExitIteration

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {V : Type*} [TopologicalSpace V]

/-- Holding a cadlag path fixed after T preserves the cadlag property. -/
theorem cadlag_min_time (f : ℝ → V) (hf : IsCadlag f) (T : ℝ) :
    IsCadlag (fun t => f (min t T)) := by
  constructor
  · intro t
    by_cases ht : t < T
    · have he : ∀ᶠ s in 𝓝[>] t, (fun s => f (min s T)) s = f s := by
        have hm : ∀ᶠ s in 𝓝[>] t, s < T :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
        filter_upwards [hm] with s hs using congrArg f (min_eq_left hs.le)
      exact (hf.isRightContinuous t).congr_of_eventuallyEq he
        (congrArg f (min_eq_left ht.le))
    · have hTt := le_of_not_gt ht
      have he : ∀ᶠ s in 𝓝[>] t, f T = f (min s T) := by
        have hm : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
        filter_upwards [hm] with s hs using congrArg f (min_eq_right (hTt.trans hs.le)).symm
      change Tendsto (fun s => f (min s T)) (𝓝[>] t) (𝓝 (f (min t T)))
      rw [min_eq_right hTt]
      exact (tendsto_const_nhds (x := f T)).congr' he
  · intro t
    by_cases ht : t ≤ T
    · obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT t
      refine ⟨l, hl.congr' ?_⟩
      have hm : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
      filter_upwards [hm] with s hs using congrArg f (min_eq_left (hs.le.trans ht)).symm
    · have hTt : T < t := lt_of_not_ge ht
      refine ⟨f T, tendsto_const_nhds.congr' ?_⟩
      have hm : ∀ᶠ s in 𝓝[<] t, T < s :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hTt)
      filter_upwards [hm] with s hs using congrArg f (min_eq_right hs.le).symm

/-- Holding a cadlag path fixed before a preserves the cadlag property. -/
theorem cadlag_max_time (f : ℝ → V) (hf : IsCadlag f) (a : ℝ) :
    IsCadlag (fun t => f (max t a)) := by
  constructor
  · intro t
    by_cases ht : a ≤ t
    · have he : ∀ᶠ s in 𝓝[>] t, (fun s => f (max s a)) s = f s := by
        have hm : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
        filter_upwards [hm] with s hs using congrArg f (max_eq_left (ht.trans hs.le))
      exact (hf.isRightContinuous t).congr_of_eventuallyEq he
        (congrArg f (max_eq_left ht))
    · have hta : t < a := lt_of_not_ge ht
      have he : ∀ᶠ s in 𝓝[>] t, f a = f (max s a) := by
        have hm : ∀ᶠ s in 𝓝[>] t, s < a :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hta)
        filter_upwards [hm] with s hs using congrArg f (max_eq_right hs.le).symm
      change Tendsto (fun s => f (max s a)) (𝓝[>] t) (𝓝 (f (max t a)))
      rw [max_eq_right hta.le]
      exact (tendsto_const_nhds (x := f a)).congr' he
  · intro t
    by_cases ht : a < t
    · obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT t
      refine ⟨l, hl.congr' ?_⟩
      have hm : ∀ᶠ s in 𝓝[<] t, a < s :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)
      filter_upwards [hm] with s hs using congrArg f (max_eq_left hs.le).symm
    · have hta : t ≤ a := le_of_not_gt ht
      refine ⟨f a, tendsto_const_nhds.congr' ?_⟩
      have hm : ∀ᶠ s in 𝓝[<] t, s < t := self_mem_nhdsWithin
      filter_upwards [hm] with s hs using congrArg f (max_eq_right (hs.le.trans hta)).symm

section Metric
variable {W : Type*} [MetricSpace W]

/-- Local finiteness on a compact trading horizon gives a finite-range extension. -/
theorem locally_finite_clamped_range (f : ℝ → W) (hf : IsCadlag f)
    (a T : ℝ) (ha : a ≤ T) (E : Set W)
    (hE : ∀ B : Set W, Bornology.IsBounded B → (E ∩ B).Finite)
    (hrange : ∀ t ∈ Icc a T, f t ∈ E) :
    (Set.range (fun t => f (min (max t a) T))).Finite := by
  have hb := isBounded_image_of_isCadlag_of_isCompact hf (s := Icc a T) isCompact_Icc
  have hF := hE (f '' Icc a T) hb
  apply hF.subset
  rintro x ⟨t, rfl⟩
  have ht : min (max t a) T ∈ Icc a T :=
    ⟨le_min (le_max_right _ _) ha, min_le_right _ _⟩
  exact ⟨hrange _ ht, ⟨_, ht, rfl⟩⟩

end Metric

section Process
variable {Ω W : Type*} [MeasurableSpace Ω] [NormedAddCommGroup W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

omit [NormedAddCommGroup W] [BorelSpace W] [SecondCountableTopology W] in
/-- The clamped process stays adapted when its initial price is deterministic. -/
theorem clamped_price_adapted (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → W) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (a T : ℝ) (ha : a ≤ T) (s₀ : W) (hinit : ∀ ω, S a ω = s₀) :
    ∀ t, Measurable[𝓕 t] (fun ω => S (min (max t a) T) ω) := by
  intro t
  by_cases ht : a ≤ t
  · rw [max_eq_left ht]
    exact (hadapt _).mono (𝓕.mono (min_le_left _ _)) le_rfl
  · have hta := le_of_not_ge ht
    simp only [max_eq_right hta, min_eq_left ha]
    have he : (fun ω => S a ω) = fun _ => s₀ := funext hinit
    rw [he]
    exact measurable_const

/-- No progressive-measurability assumption is needed for the adapted price exits. -/
theorem adapted_price_exit_sequence_stopping_times
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → W) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hright : ∀ ω, IsRightContinuous (fun t => S t ω)) (a T : ℝ) :
    ∀ n, IsStoppingTime 𝓕 (fun ω => (priceExitSequence S a T n ω : WithTop ℝ)) := by
  exact price_exit_sequence_stopping_times 𝓕 S
    (adapted_right_continuous_progressive 𝓕 S hadapt hright) hright a T

/-- On a compact horizon, the locally finite price assumption supplies both
stopping times and pathwise termination of their capped exit sequence. -/
theorem locally_finite_price_exit_sequence
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) [𝓕.IsRightContinuous]
    (S : ℝ → Ω → W) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (a T : ℝ) (ha : a ≤ T) (s₀ : W) (hinit : ∀ ω, S a ω = s₀)
    (E : Set W) (hE : ∀ B : Set W, Bornology.IsBounded B → (E ∩ B).Finite)
    (hstates : ∀ ω t, t ∈ Icc a T → S t ω ∈ E) :
    let C := fun t ω => S (min (max t a) T) ω
    (∀ n, IsStoppingTime 𝓕 (fun ω => (priceExitSequence C a T n ω : WithTop ℝ))) ∧
      ∀ ω, ∃ N, ∀ k, priceExitSequence C a T (N+k) ω = T := by
  let C := fun t ω => S (min (max t a) T) ω
  have hC : ∀ ω, IsCadlag (fun t => C t ω) := fun ω =>
    cadlag_max_time (fun t => S (min t T) ω) (cadlag_min_time _ (hcad ω) T) a
  refine ⟨adapted_price_exit_sequence_stopping_times 𝓕 C
    (clamped_price_adapted 𝓕 S hadapt a T ha s₀ hinit)
    (fun ω => (hC ω).isRightContinuous) a T, ?_⟩
  intro ω
  exact price_exit_sequence_eventually_terminal C a T ha ω (hC ω)
    (locally_finite_clamped_range (fun t => S t ω) (hcad ω) a T ha E hE (hstates ω))

end Process

#print axioms locally_finite_clamped_range
#print axioms clamped_price_adapted
#print axioms adapted_price_exit_sequence_stopping_times
#print axioms locally_finite_price_exit_sequence
#print axioms cadlag_min_time
#print axioms cadlag_max_time
end FTDAP
