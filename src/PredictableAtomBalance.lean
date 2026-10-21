import BalancedAtomicGains

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Zero expected signed atom tests on predictable generating rectangles imply
balance of the entire positive and negative predictable atomic measures. -/
theorem predictable_atom_measure_balance
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (atom : ℕ → Ω → NNReal × Ω)
    (ha : ∀ n, @Measurable Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable (atom n))
    (d : ℕ → Ω → ℝ) (hd : ∀ n, Measurable (d n))
    (J : Ω → Finset ℕ) (hsupport : ∀ ω n, n ∉ J ω → d n ω = 0)
    (K : ℝ) (hmass : ∀ᵐ ω ∂P, (∑ n ∈ J ω, |d n ω|) ≤ K)
    (hzero : ∀ A, MeasurableSet[𝓕 0] A →
      (∫ ω, ∑ n ∈ J ω, d n ω * ({(0 : NNReal)} ×ˢ A).indicator (fun _ => (1 : ℝ)) (atom n ω) ∂P) = 0)
    (hrect : ∀ t A, MeasurableSet[𝓕 t] A →
      (∫ ω, ∑ n ∈ J ω, d n ω * (Ioi t ×ˢ A).indicator (fun _ => (1 : ℝ)) (atom n ω) ∂P) = 0) :
    let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
    jumpMeasure P atom (fun n ω => ENNReal.ofReal (max (d n ω) 0)) =
      jumpMeasure P atom (fun n ω => ENNReal.ofReal (max (-d n ω) 0)) := by
  classical
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  let p := fun n ω => max (d n ω) 0
  let m := fun n ω => max (-d n ω) 0
  let μ := jumpMeasure P atom (fun n ω => ENNReal.ofReal (p n ω))
  let ν := jumpMeasure P atom (fun n ω => ENNReal.ofReal (m n ω))
  have hp : ∀ n, Measurable (p n) := fun n => (hd n).max measurable_const
  have hm : ∀ n, Measurable (m n) := fun n => (hd n).neg.max measurable_const
  have hps : ∀ ω n, n ∉ J ω → p n ω = 0 := by
    intro ω n hn
    simp only [p, hsupport ω n hn, max_self]
  have hms : ∀ ω n, n ∉ J ω → m n ω = 0 := by
    intro ω n hn
    simp only [m, hsupport ω n hn, neg_zero, max_self]
  have hpb : ∀ᵐ ω ∂P, (∑ n ∈ J ω, p n ω) ≤ K := hmass.mono (fun ω hω =>
    (Finset.sum_le_sum (fun n _ => max_le (le_abs_self _) (abs_nonneg _))).trans hω)
  have hmb : ∀ᵐ ω ∂P, (∑ n ∈ J ω, m n ω) ≤ K := hmass.mono (fun ω hω =>
    (Finset.sum_le_sum (fun n _ => max_le (neg_le_abs _) (abs_nonneg _))).trans hω)
  let : IsFiniteMeasure μ := ⟨(nonnegative_atomic_measure_mass_le P atom ha p hp
    (fun _ _ => le_max_right _ _) J hps K hpb).trans_lt ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure ν := ⟨(nonnegative_atomic_measure_mass_le P atom ha m hm
    (fun _ _ => le_max_right _ _) J hms K hmb).trans_lt ENNReal.ofReal_lt_top⟩
  have htest : ∀ A : Set (NNReal × Ω), MeasurableSet A →
      (∫ ω, ∑ n ∈ J ω, d n ω * A.indicator (fun _ => (1 : ℝ)) (atom n ω) ∂P) = 0 → μ A = ν A := by
    intro A hA htestA
    have hAb : ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
      intro x
      by_cases hx : x ∈ A <;> simp [hx]
    have he := atomic_integral_signed_decomposition P atom ha d hd J hsupport K hmass
      _ (measurable_const.indicator hA) 1 zero_le_one hAb
    rw [htestA] at he
    change (∫ x, A.indicator 1 x ∂μ) - (∫ x, A.indicator 1 x ∂ν) = 0 at he
    have hreal : μ.real A - ν.real A = 0 := by
      rwa [integral_indicator_one hA, integral_indicator_one hA] at he
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp (sub_eq_zero.mp hreal)
  apply predictable_measure_ext 𝓕 μ ν
  · intro A hA
    exact htest _ (measurableSet_predictable_singleton_bot_prod hA) (hzero A hA)
  · intro t A hA
    exact htest _ (measurableSet_predictable_Ioi_prod hA) (hrect t A hA)

#print axioms predictable_atom_measure_balance
end FTDAP
