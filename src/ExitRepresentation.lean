import ActiveJumps
import Mathlib.Tactic.Abel

open MeasureTheory Set Filter Function
open scoped Topology
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {V : Type*} [NormedAddCommGroup V]

/-- Before the next exit the state is constant, so its left limit at that exit
is the state at the previous exit. -/
theorem exit_left_limit (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (t T : ℝ) (ht : t ≤ T)
    (hstrict : t < nextExitTime f t T) :
    leftLim f (nextExitTime f t T) = f t := by
  have hp := next_exit_properties f hf.isRightContinuous hfinite t T ht
  have he : ∀ᶠ s in 𝓝[<] (nextExitTime f t T), f s = f t := by
    have hl : ∀ᶠ s in 𝓝[<] (nextExitTime f t T), t < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hstrict)
    have hr : ∀ᶠ s in 𝓝[<] (nextExitTime f t T), s < nextExitTime f t T := self_mem_nhdsWithin
    filter_upwards [hl, hr] with s hts hs
    exact hp.2.2.2.1 s hts.le hs
  have hc : Tendsto f (𝓝[<] (nextExitTime f t T)) (𝓝 (f t)) := by
    apply (tendsto_const_nhds (x := f t)).congr'
    filter_upwards [he] with s hs using hs.symm
  exact tendsto_nhds_unique (tendsto_leftLim_of_tendsto (hf.tendsto_nhdsLT _)) hc

/-- Telescoping along exits recovers the price at every intermediate time. -/
theorem exit_prefix_representation (f : ℝ → V) (hf : IsRightContinuous f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T) (t : ℝ) (hat : a ≤ t) :
    ∀ n, f (min t (exitSequence f a T n)) - f a =
      ∑ k ∈ Finset.range n, if exitSequence f a T (k+1) ≤ t then
        f (exitSequence f a T (k+1)) - f (exitSequence f a T k) else 0 := by
  intro n
  induction n with
  | zero => simp [exitSequence, min_eq_right hat]
  | succ n ih =>
    have hb := exit_sequence_bounds f hf hfinite a T ha n
    have hp := next_exit_properties f hf hfinite (exitSequence f a T n) T hb.2.1
    have hmono : exitSequence f a T n ≤ exitSequence f a T (n+1) := hp.1
    rw [Finset.sum_range_succ, ← ih]
    by_cases hn : exitSequence f a T (n+1) ≤ t
    · rw [ite_eq_left hn, min_eq_right hn, min_eq_right (hmono.trans hn)]
      abel
    · rw [ite_eq_right hn, add_zero, min_eq_left (le_of_not_ge hn)]
      by_cases hprev : exitSequence f a T n ≤ t
      · rw [min_eq_right hprev]
        have he : f t = f (exitSequence f a T n) :=
          hp.2.2.2.1 t hprev (lt_of_not_ge hn)
        rw [he]
      · rw [min_eq_left (le_of_not_ge hprev)]

/-- The finite Stieltjes representation uses a path-dependent, finite exit count. -/
theorem finite_exit_representation (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T) :
    ∃ N, (∀ k, exitSequence f a T (N+k) = T) ∧
      ∀ t ∈ Icc a T, f t - f a =
      ∑ k ∈ Finset.range N, if exitSequence f a T (k+1) ≤ t then
        f (exitSequence f a T (k+1)) - f (exitSequence f a T k) else 0 := by
  obtain ⟨N, hN⟩ := exit_sequence_eventually_terminal f hf hfinite a T ha
  refine ⟨N, hN, ?_⟩
  intro t ht
  have he := exit_prefix_representation f hf.isRightContinuous hfinite a T ha t ht.1 N
  have hzero : exitSequence f a T N = T := by simpa using hN 0
  simpa only [hzero, min_eq_left ht.2] using he

/-- The finite representation uses actual left-limit jump increments; repeated
terminal times and zero increments make no contribution. -/
theorem finite_exit_actual_jump_representation (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T) :
    let τ := exitSequence f a T
    let Δ := fun k => f (τ (k+1)) - leftLim f (τ (k+1))
    ∃ N, (∀ k, τ (N+k) = T) ∧ ∀ t ∈ Icc a T, f t - f a =
      ∑ k ∈ Finset.range N, if τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t
        then Δ k else 0 := by
  let τ := exitSequence f a T
  let Δ := fun k => f (τ (k+1)) - leftLim f (τ (k+1))
  obtain ⟨N, hterm, hN⟩ := finite_exit_representation f hf hfinite a T ha
  refine ⟨N, hterm, ?_⟩
  intro t ht
  rw [hN t ht]
  apply Finset.sum_congr rfl
  intro k hk
  have hb := exit_sequence_bounds f hf.isRightContinuous hfinite a T ha k
  have hp := next_exit_properties f hf.isRightContinuous hfinite (τ k) T hb.2.1
  have hmono : τ k ≤ τ (k+1) := hp.1
  by_cases hs : τ k < τ (k+1)
  · have hl : leftLim f (τ (k+1)) = f (τ k) :=
      exit_left_limit f hf hfinite (τ k) T hb.2.1 hs
    have hd : f (τ (k+1)) - f (τ k) = Δ k := by dsimp [Δ]; rw [hl]
    change (if τ (k+1) ≤ t then f (τ (k+1)) - f (τ k) else 0) =
      (if τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t then Δ k else 0)
    rw [hd]
    by_cases hz : Δ k = 0 <;> simp [hs, hz]
  · have he : τ k = τ (k+1) := le_antisymm hmono (le_of_not_gt hs)
    change (if τ (k+1) ≤ t then f (τ (k+1)) - f (τ k) else 0) =
      (if τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t then Δ k else 0)
    simp [he]

/-- Any finite set identifying precisely the active exits gives the actual
Stieltjes sum, simultaneously at every time in the trading horizon. -/
theorem exit_representation_active_set (f : ℝ → V) (hf : IsCadlag f)
    (hfinite : (Set.range f).Finite) (a T : ℝ) (ha : a ≤ T)
    (jumps : Finset ℕ)
    (hmem : ∀ k, k ∈ jumps ↔ exitSequence f a T k < exitSequence f a T (k+1) ∧
      f (exitSequence f a T (k+1)) - leftLim f (exitSequence f a T (k+1)) ≠ 0) :
    ∀ t ∈ Icc a T, f t - f a = ∑ k ∈ jumps,
      if exitSequence f a T (k+1) ≤ t then
        f (exitSequence f a T (k+1)) - leftLim f (exitSequence f a T (k+1)) else 0 := by
  let τ := exitSequence f a T
  let Δ := fun k => f (τ (k+1)) - leftLim f (τ (k+1))
  obtain ⟨N, hterm, hrep⟩ := finite_exit_actual_jump_representation f hf hfinite a T ha
  have hsub : jumps ⊆ Finset.range N := by
    intro k hk
    apply Finset.mem_range.mpr
    by_contra hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    have ha' := (hmem _).mp hk
    have hnext : τ (N+j+1) = T := by simpa only [Nat.add_assoc] using hterm (j+1)
    change τ (N+j) < τ (N+j+1) ∧ Δ (N+j) ≠ 0 at ha'
    have hnow : τ (N+j) = T := hterm j
    rw [hnow, hnext] at ha'
    exact lt_irrefl T ha'.1
  intro t ht
  rw [hrep t ht]
  symm
  calc
    _ = ∑ k ∈ jumps, if τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t then Δ k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := (hmem k).mp hk
      change (if τ (k+1) ≤ t then Δ k else 0) =
        (if τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t then Δ k else 0)
      have hact : τ k < τ (k+1) ∧ Δ k ≠ 0 := hk'
      by_cases htime : τ (k+1) ≤ t
      · rw [ite_eq_left htime, ite_eq_left ⟨hact.1, hact.2, htime⟩]
      · rw [ite_eq_right htime, ite_eq_right (fun h => htime h.2.2)]
    _ = ∑ k ∈ Finset.range N,
        if τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t then Δ k else 0 := by
      apply Finset.sum_subset hsub
      intro k hk hnot
      have hn : ¬ (τ k < τ (k+1) ∧ Δ k ≠ 0) := fun h => hnot ((hmem k).mpr h)
      by_cases hcond : τ k < τ (k+1) ∧ Δ k ≠ 0 ∧ τ (k+1) ≤ t
      · exact (hn ⟨hcond.1, hcond.2.1⟩).elim
      · exact ite_eq_right hcond

#print axioms exit_representation_active_set
#print axioms finite_exit_actual_jump_representation
#print axioms exit_left_limit
#print axioms exit_prefix_representation
#print axioms finite_exit_representation
end FTDAP
