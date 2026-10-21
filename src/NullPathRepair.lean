import ConstructedTradingGains

open MeasureTheory Set Filter Function
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V]

/-- Replace exceptional paths by the initial constant path and clamp the time
horizon. Completeness is used only to make the exceptional set measurable at
all times. -/
theorem repair_exceptional_price_paths
    (P : Measure Ω) (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (T : NNReal) (s₀ : V) (N : Set Ω) (hnull : P N = 0)
    (hN : ∀ t, MeasurableSet[𝓕 t] N)
    (hcad : ∀ ω ∉ N, IsCadlag (fun t => S t ω))
    (hinit : ∀ ω ∉ N, S 0 ω = s₀)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hstates : ∀ ω ∉ N, ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E) :
    ∃ R : ℝ → Ω → V,
      (∀ t, Measurable[𝓕 t] (R t)) ∧
      (∀ ω, IsCadlag (fun t => R t ω)) ∧
      (∀ ω, (Set.range (fun t => R t ω)).Finite) ∧
      (∀ ω, R 0 ω = s₀) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), R t ω = S t ω := by
  classical
  let D : ℝ → Ω → V := fun t ω => if ω ∈ N then s₀ else S t ω
  have hDadapt : ∀ t, Measurable[𝓕 t] (D t) := fun t =>
    measurable_const.ite (hN t) (hadapt t)
  have hDinit : ∀ ω, D 0 ω = s₀ := by
    intro ω
    by_cases hn : ω ∈ N
    · simp only [D, ite_eq_left hn]
    · simp only [D, ite_eq_right hn, hinit ω hn]
  have hDcad : ∀ ω, IsCadlag (fun t => D t ω) := by
    intro ω
    by_cases hn : ω ∈ N
    · simpa only [D, ite_eq_left hn] using (IsCadlag.const (c := s₀) : IsCadlag (fun _ : ℝ => s₀))
    · simpa only [D, ite_eq_right hn] using hcad ω hn
  let R : ℝ → Ω → V := fun t ω => D (min (max t 0) (T : ℝ)) ω
  refine ⟨R, clamped_price_adapted 𝓕 D hDadapt 0 (T : ℝ) T.2 s₀ hDinit, ?_, ?_, ?_, ?_⟩
  · intro ω
    exact cadlag_max_time (fun t => D (min t (T : ℝ)) ω)
      (cadlag_min_time _ (hDcad ω) (T : ℝ)) 0
  · intro ω
    by_cases hn : ω ∈ N
    · have he : (fun t => R t ω) = fun _ => s₀ := by
        funext t
        exact ite_eq_left hn
      rw [he]
      exact Set.finite_range_const
    · have hf := locally_finite_clamped_range (fun t => S t ω) (hcad ω hn)
        0 (T : ℝ) T.2 E hE (hstates ω hn)
      simpa only [R, D, ite_eq_right hn] using hf
  · intro ω
    change D (min (max 0 0) (T : ℝ)) ω = s₀
    rw [max_self, min_eq_left (show (0 : ℝ) ≤ (T : ℝ) from T.2)]
    exact hDinit ω
  · have hg : ∀ᵐ ω ∂P, ω ∉ N := by
      exact compl_mem_ae_iff.mpr hnull
    filter_upwards [hg] with ω hn
    intro t ht
    change (if ω ∈ N then s₀ else S (min (max t 0) (T : ℝ)) ω) = S t ω
    rw [ite_eq_right hn, max_eq_left ht.1, min_eq_left ht.2]

/-- Almost-sure path assumptions yield an indistinguishable regular version
when every null set belongs to every time sigma-algebra. -/
theorem regular_price_version
    (P : Measure Ω) (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (S : ℝ → Ω → V) (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (T : NNReal) (s₀ : V)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧ S 0 ω = s₀ ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E) :
    ∃ R : ℝ → Ω → V,
      (∀ t, Measurable[𝓕 t] (R t)) ∧
      (∀ ω, IsCadlag (fun t => R t ω)) ∧
      (∀ ω, (Set.range (fun t => R t ω)).Finite) ∧
      (∀ ω, R 0 ω = s₀) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), R t ω = S t ω := by
  let N := {ω | ¬ (IsCadlag (fun t => S t ω) ∧ S 0 ω = s₀ ∧
    ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)}
  have hn : P N = 0 := ae_iff.mp hpath
  have hg : ∀ ω ∉ N, IsCadlag (fun t => S t ω) ∧ S 0 ω = s₀ ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E := by
    intro ω h
    exact Classical.not_not.mp h
  exact repair_exceptional_price_paths P 𝓕 S hadapt T s₀ N hn (hcomplete N hn)
    (fun ω h => (hg ω h).1) (fun ω h => (hg ω h).2.1) E hE (fun ω h => (hg ω h).2.2)

#print axioms repair_exceptional_price_paths
#print axioms regular_price_version
end FTDAP
