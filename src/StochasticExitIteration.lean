import ExitIteration
import ContinuousExit

open MeasureTheory Set WithTop
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Capping an extended stopping time gives a finite real stopping time. -/
theorem capped_stopping_time_real (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (τ : Ω → WithTop ℝ) (hτ : IsStoppingTime 𝓕 τ) (T : ℝ) :
    IsStoppingTime 𝓕 (fun ω => (((min (τ ω) (T : WithTop ℝ)).untopA : ℝ) : WithTop ℝ)) := by
  convert hτ.min_const T using 1
  funext ω
  have hn : min (τ ω) (T : WithTop ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top coe_ne_top (min_le_right _ _)
  lift min (τ ω) (T : WithTop ℝ) to ℝ using hn with r hr
  rfl

noncomputable def nextPriceExit (S : ℝ → Ω → V) (σ : Ω → ℝ) (T : ℝ) : Ω → ℝ :=
  fun ω => (min (hittingAfter (fun s ω' => S s ω' - S (σ ω') ω')
    ({0}ᶜ : Set V) (σ ω) ω) (T : WithTop ℝ)).untopA

/-- Recursive capped departures remain stopping times in the original filtration. -/
theorem next_price_exit_stopping_time (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    [𝓕.IsRightContinuous] (S : ℝ → Ω → V) (hprog : IsStronglyProgressive 𝓕 S)
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω))
    (σ : Ω → ℝ) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ))) (T : ℝ) :
    IsStoppingTime 𝓕 (fun ω => (nextPriceExit S σ T ω : WithTop ℝ)) := by
  exact capped_stopping_time_real 𝓕 _
    (next_price_change_stopping_time 𝓕 S hprog hright σ hσ) T

noncomputable def priceExitSequence (S : ℝ → Ω → V) (a T : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => a
  | n+1 => nextPriceExit S (priceExitSequence S a T n) T

/-- Every member of the recursively defined price-exit sequence is a stopping time. -/
theorem price_exit_sequence_stopping_times (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    [𝓕.IsRightContinuous] (S : ℝ → Ω → V) (hprog : IsStronglyProgressive 𝓕 S)
    (hright : ∀ ω, IsRightContinuous (fun s => S s ω)) (a T : ℝ) :
    ∀ n, IsStoppingTime 𝓕 (fun ω => (priceExitSequence S a T n ω : WithTop ℝ)) := by
  intro n
  induction n with
  | zero => exact isStoppingTime_const (f := 𝓕) (i := a)
  | succ n ih => exact next_price_exit_stopping_time 𝓕 S hprog hright _ ih T

omit [MeasurableSpace Ω] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- The stochastic hitting-time construction agrees pathwise with capped exits. -/
theorem next_price_exit_eq (S : ℝ → Ω → V) (σ : Ω → ℝ) (T : ℝ) (ω : Ω) :
    nextPriceExit S σ T ω = nextExitTime (fun s => S s ω) (σ ω) T := by
  classical
  simp only [nextPriceExit, hittingAfter, mem_compl_iff, mem_singleton_iff,
    sub_eq_zero, nextExitTime]
  by_cases hg : ∃ s, σ ω ≤ s ∧ S s ω ≠ S (σ ω) ω
  · rw [ite_eq_left hg]
    have hb : BddBelow {s | σ ω ≤ s ∧ S s ω ≠ S (σ ω) ω} :=
      ⟨σ ω, fun _ h => h.1⟩
    by_cases he : ∃ s, σ ω ≤ s ∧ s ≤ T ∧ S s ω ≠ S (σ ω) ω
    · rw [ite_eq_left he]
      obtain ⟨s, hσs, hsT, hne⟩ := he
      have hi := (csInf_le hb ⟨hσs, hne⟩).trans hsT
      rw [← WithTop.coe_min, min_eq_left hi]
      rfl
    · rw [ite_eq_right he]
      have hi : T ≤ sInf {s | σ ω ≤ s ∧ S s ω ≠ S (σ ω) ω} := by
        apply le_csInf hg
        intro s hs
        by_contra hn
        exact he ⟨s, hs.1, (lt_of_not_ge hn).le, hs.2⟩
      rw [← WithTop.coe_min, min_eq_right hi]
      rfl
  · rw [ite_eq_right hg]
    have he : ¬ ∃ s, σ ω ≤ s ∧ s ≤ T ∧ S s ω ≠ S (σ ω) ω := by
      rintro ⟨s, hs, _, hne⟩
      exact hg ⟨s, hs, hne⟩
    rw [ite_eq_right he]
    rfl

omit [MeasurableSpace Ω] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Every stochastic iterate agrees with the deterministic exit iteration. -/
theorem price_exit_sequence_eq (S : ℝ → Ω → V) (a T : ℝ) (ω : Ω) :
    ∀ n, priceExitSequence S a T n ω = exitSequence (fun s => S s ω) a T n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [priceExitSequence, next_price_exit_eq, exitSequence, ih]

omit [MeasurableSpace Ω] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- For cadlag finite-range paths, the stopping-time sequence is eventually T. -/
theorem price_exit_sequence_eventually_terminal (S : ℝ → Ω → V) (a T : ℝ)
    (ha : a ≤ T) (ω : Ω) (hcad : IsCadlag (fun s => S s ω))
    (hfinite : (Set.range (fun s => S s ω)).Finite) :
    ∃ N, ∀ k, priceExitSequence S a T (N+k) ω = T := by
  obtain ⟨N, hN⟩ := exit_sequence_eventually_terminal (fun s => S s ω) hcad hfinite a T ha
  exact ⟨N, fun k => (price_exit_sequence_eq S a T ω (N+k)).trans (hN k)⟩

#print axioms next_price_exit_eq
#print axioms price_exit_sequence_eq
#print axioms price_exit_sequence_eventually_terminal
#print axioms capped_stopping_time_real
#print axioms next_price_exit_stopping_time
#print axioms price_exit_sequence_stopping_times
end FTDAP
