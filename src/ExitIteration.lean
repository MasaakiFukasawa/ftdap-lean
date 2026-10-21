import DiscreteExit

open Set Filter TopologicalSpace
open scoped Topology
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {V : Type*} [MetricSpace V]

/-- The next departure, capped at the terminal time; absent departures give T. -/
noncomputable def nextExitTime (f : ℝ → V) (t T : ℝ) : ℝ :=
  if ∃ s, t ≤ s ∧ s ≤ T ∧ f s ≠ f t then
    sInf {s | t ≤ s ∧ f s ≠ f t} else T

/-- Capping the attained exit preserves order and gives constancy before it. -/
theorem next_exit_properties (f : ℝ → V) (hf : IsRightContinuous f)
    (hfinite : (Set.range f).Finite) (t T : ℝ) (ht : t ≤ T) :
    t ≤ nextExitTime f t T ∧ nextExitTime f t T ≤ T ∧
    (t < T → t < nextExitTime f t T) ∧
    (∀ s, t ≤ s → s < nextExitTime f t T → f s = f t) ∧
    (nextExitTime f t T < T → ¬ ContinuousAt f (nextExitTime f t T)) := by
  classical
  unfold nextExitTime
  split_ifs with hex
  · obtain ⟨s, hts, hsT, hne⟩ := hex
    have he : ∃ s, t ≤ s ∧ f s ≠ f t := ⟨s, hts, hne⟩
    obtain ⟨hlt, _, hbefore⟩ := finite_range_first_exit_attained f hf hfinite t he
    have hb : BddBelow {s | t ≤ s ∧ f s ≠ f t} := ⟨t, fun _ h => h.1⟩
    have hle := (csInf_le hb ⟨hts, hne⟩).trans hsT
    exact ⟨hlt.le, hle, fun _ => hlt, hbefore,
      fun _ => finite_range_exit_is_jump f hf hfinite t he⟩
  · refine ⟨ht, le_rfl, fun h => h, ?_, fun h => (lt_irrefl T h).elim⟩
    intro s hts hsT
    by_contra hne
    exact hex ⟨s, hts, hsT.le, hne⟩

/-- A finite-range cadlag path has finitely many discontinuities on [a,T]. -/
theorem finite_range_cadlag_jumps (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) :
    {t ∈ Icc a T | ¬ ContinuousAt f t}.Finite := by
  let : DiscreteTopology (Set.range f) := isDiscrete_iff_discreteTopology.mp hfinite.isDiscrete
  let g : ℝ → Set.range f := fun t => ⟨f t, Set.mem_range_self t⟩
  have hg : IsCadlag g := cadlag_subtype_closed f hf _ hfinite.isClosed
    (fun t => Set.mem_range_self t)
  have hgood := discrete_cadlag_finite_jumps g hg (Icc a T) isCompact_Icc
  apply hgood.subset
  intro t ht
  refine ⟨ht.1, ?_⟩
  intro hc
  exact ht.2 (continuous_subtype_val.continuousAt.comp hc)

/-- Iterate capped first departures from the initial time. -/
noncomputable def exitSequence (f : ℝ → V) (a T : ℝ) : ℕ → ℝ
  | 0 => a
  | n+1 => nextExitTime f (exitSequence f a T n) T

/-- The iterates stay in the horizon and increase strictly until reaching T. -/
theorem exit_sequence_bounds (f : ℝ → V) (hf : IsRightContinuous f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T) :
    ∀ n, a ≤ exitSequence f a T n ∧ exitSequence f a T n ≤ T ∧
      (exitSequence f a T n < T → exitSequence f a T n < exitSequence f a T (n+1)) := by
  intro n
  have hb : ∀ n, a ≤ exitSequence f a T n ∧ exitSequence f a T n ≤ T := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, ha⟩
    | succ n ih =>
      have hp := next_exit_properties f hf hfinite _ T ih.2
      exact ⟨ih.1.trans hp.1, hp.2.1⟩
  exact ⟨(hb n).1, (hb n).2,
    (next_exit_properties f hf hfinite _ T (hb n).2).2.2.1⟩

/-- A finite-range cadlag path's iterated departures reach the terminal time.
The required number of iterations may depend on the path. -/
theorem exit_sequence_reaches_terminal (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T) :
    ∃ N, exitSequence f a T N = T := by
  by_contra h
  push Not at h
  have hb := exit_sequence_bounds f hf.isRightContinuous hfinite a T ha
  have hlt : ∀ n, exitSequence f a T n < T :=
    fun n => lt_of_le_of_ne (hb n).2.1 (h n)
  have hs : StrictMono (exitSequence f a T) :=
    strictMono_nat_of_lt_succ (fun n => (hb n).2.2 (hlt n))
  let K := {t ∈ Icc a T | ¬ ContinuousAt f t}
  have hK : K.Finite := finite_range_cadlag_jumps f hf hfinite a T
  have hrange : (Set.range (fun n => exitSequence f a T (n+1))).Finite := by
    apply hK.subset
    rintro t ⟨n, rfl⟩
    refine ⟨⟨(hb (n+1)).1, (hb (n+1)).2.1⟩, ?_⟩
    exact (next_exit_properties f hf.isRightContinuous hfinite _ T
      (hb n).2.1).2.2.2.2 (hlt (n+1))
  have hi : Function.Injective (fun n => exitSequence f a T (n+1)) := by
    intro n m he
    exact Nat.succ.inj (hs.injective he)
  exact hrange.not_infinite (Set.infinite_range_of_injective hi)

/-- Once the terminal time is reached, all later iterates remain there. -/
theorem exit_sequence_eventually_terminal (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T) :
    ∃ N, ∀ k, exitSequence f a T (N+k) = T := by
  obtain ⟨N, hN⟩ := exit_sequence_reaches_terminal f hf hfinite a T ha
  refine ⟨N, ?_⟩
  intro k
  induction k with
  | zero => simpa using hN
  | succ k ih =>
    rw [Nat.add_succ, exitSequence, ih]
    have hp := next_exit_properties f hf.isRightContinuous hfinite T T le_rfl
    exact le_antisymm hp.2.1 hp.1

#print axioms exit_sequence_bounds
#print axioms exit_sequence_reaches_terminal
#print axioms exit_sequence_eventually_terminal
#print axioms next_exit_properties
#print axioms finite_range_cadlag_jumps
end FTDAP
