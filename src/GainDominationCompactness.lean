import AtomGainLimits
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω α ι V : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [LinearOrder ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The weighted Hilbert compactness argument preserves admissibility and
terminal domination of an almost-surely convergent claim sequence. All convex
average compatibility with gains and the null-set transports are derived. -/
theorem gain_domination_compactness (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (H : ℕ → Lp V 2 (jumpMeasure P atom weight)) (R a : ℝ) (T : ι)
    (payoff : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hbounded : ∀ n, ‖H n‖ ≤ R)
    (hadm : ∀ n, ∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ (H n) t ω)
    (hdom : ∀ n, ∀ᵐ ω ∂P, payoff n ω ≤ atomGain jumps τ atom Δ (H n) T ω)
    (hpayoff : ∀ᵐ ω ∂P, Tendsto (fun n => payoff n ω) atTop (𝓝 (f ω))) :
    ∃ Y : Lp V 2 (jumpMeasure P atom weight),
      (∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ Y t ω) ∧
      ∀ᵐ ω ∂P, f ω ≤ atomGain jumps τ atom Δ Y T ω := by
  classical
  obtain ⟨G, Y, hconv, hatoms⟩ := komlos_jump_atoms P atom weight ha hw H R hbounded
  have hadmG : ∀ n, ∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ (G n) t ω := by
    intro n
    apply convexHull_min (t := {Z : Lp V 2 (jumpMeasure P atom weight) |
      ∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ Z t ω}) ?_
      (lp_atom_gain_constraints_convex P jumps τ atom Δ weight ha hw hpositive (fun _ _ => -a))
      (hconv n)
    rintro _ ⟨k, _, rfl⟩
    exact hadm k
  have hadmY := atom_gain_lower_bounds_pass P jumps τ atom Δ weight hpositive
    (fun n => G n) Y (fun _ _ => -a) hatoms hadmG
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hε : ∀ m, 0 < ε m := by intro m; dsimp [ε]; positivity
  let lower : ℕ → ℕ → ι → Ω → ℝ := fun N m t ω =>
    if t = T ∧ ∀ k ≥ N, f ω - ε m ≤ payoff k ω then max (-a) (f ω - ε m) else -a
  have htail : ∀ N m n, N ≤ n → ∀ᵐ ω ∂P, ∀ t,
      lower N m t ω ≤ atomGain jumps τ atom Δ (G n) t ω := by
    intro N m n hn
    apply convexHull_min (t := {Z : Lp V 2 (jumpMeasure P atom weight) |
      ∀ᵐ ω ∂P, ∀ t, lower N m t ω ≤ atomGain jumps τ atom Δ Z t ω}) ?_
      (lp_atom_gain_constraints_convex P jumps τ atom Δ weight ha hw hpositive (lower N m))
      (hconv n)
    rintro _ ⟨k, hk, rfl⟩
    filter_upwards [hadm k, hdom k] with ω had hdo t
    dsimp [lower]
    split_ifs with h
    · rcases h with ⟨ht, htail⟩
      rw [ht]
      exact max_le (had T) ((htail k (hn.trans hk)).trans hdo)
    · exact had t
  have htailAE : ∀ᵐ ω ∂P, ∀ N m n, N ≤ n → ∀ t,
      lower N m t ω ≤ atomGain jumps τ atom Δ (G n) t ω := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro n
    by_cases hn : N ≤ n
    · exact (htail N m n hn).mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => (hn h).elim)
  have hgainlimits := atom_gain_limits P jumps τ atom Δ weight hpositive (fun n => G n) Y hatoms
  refine ⟨Y, hadmY, ?_⟩
  filter_upwards [htailAE, hgainlimits, hpayoff] with ω ht hl hp
  have hY : ∀ N m, lower N m T ω ≤ atomGain jumps τ atom Δ Y T ω := by
    intro N m
    exact le_of_tendsto_of_tendsto tendsto_const_nhds (hl T)
      ((eventually_ge_atTop N).mono (fun n hn => ht N m n hn T))
  have happrox : ∀ m, f ω - ε m ≤ atomGain jumps τ atom Δ Y T ω := by
    intro m
    have he : ∀ᶠ k in atTop, f ω - ε m ≤ payoff k ω :=
      ((tendsto_order.mp hp).1 _ (sub_lt_self _ (hε m))).mono (fun _ h => h.le)
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    have h := hY N m
    have hcond : T = T ∧ ∀ k ≥ N, f ω - ε m ≤ payoff k ω := ⟨rfl, hN⟩
    dsimp [lower] at h
    rw [ite_eq_left hcond] at h
    exact (le_max_right _ _).trans h
  have heps : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hf : Tendsto (fun m => f ω - ε m) atTop (𝓝 (f ω)) := by
    simpa using tendsto_const_nhds.sub heps
  exact le_of_tendsto hf (Eventually.of_forall happrox)

#print axioms gain_domination_compactness
end FTDAP
