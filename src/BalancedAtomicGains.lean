import AtomicIntegral

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Equality of the positive and negative atomic measures forces zero mean
for every bounded measurable integrand against the actual signed finite sum. -/
theorem atomic_integral_signed_decomposition
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (ha : ∀ n, Measurable (atom n))
    (d : ℕ → Ω → ℝ) (hd : ∀ n, Measurable (d n))
    (J : Ω → Finset ℕ) (hsupport : ∀ ω n, n ∉ J ω → d n ω = 0)
    (K : ℝ) (hmass : ∀ᵐ ω ∂P, (∑ n ∈ J ω, |d n ω|) ≤ K)
    (H : α → ℝ) (hH : Measurable H) (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ x, |H x| ≤ B) :
    (∫ x, H x ∂jumpMeasure P atom (fun n ω => ENNReal.ofReal (max (d n ω) 0))) -
      (∫ x, H x ∂jumpMeasure P atom (fun n ω => ENNReal.ofReal (max (-d n ω) 0))) =
      ∫ ω, ∑ n ∈ J ω, d n ω * H (atom n ω) ∂P := by
  classical
  let p := fun n ω => max (d n ω) 0
  let m := fun n ω => max (-d n ω) 0
  have hpmeas : ∀ n, Measurable (p n) := fun n => (hd n).max measurable_const
  have hmmeas : ∀ n, Measurable (m n) := fun n => (hd n).neg.max measurable_const
  have hps : ∀ ω n, n ∉ J ω → p n ω = 0 := by
    intro ω n hn
    simp only [p, hsupport ω n hn, max_self]
  have hms : ∀ ω n, n ∉ J ω → m n ω = 0 := by
    intro ω n hn
    simp only [m, hsupport ω n hn, neg_zero, max_self]
  have hpb : ∀ᵐ ω ∂P, (∑ n ∈ J ω, p n ω) ≤ K := by
    filter_upwards [hmass] with ω hω
    apply le_trans _ hω
    exact Finset.sum_le_sum (fun n _ => max_le (le_abs_self _) (abs_nonneg _))
  have hmb : ∀ᵐ ω ∂P, (∑ n ∈ J ω, m n ω) ≤ K := by
    filter_upwards [hmass] with ω hω
    apply le_trans _ hω
    exact Finset.sum_le_sum (fun n _ => max_le (neg_le_abs _) (abs_nonneg _))
  have hp := integral_finite_jump_measure P atom ha p hpmeas (fun _ _ => le_max_right _ _)
    J hps K hpb H hH B hB hHb
  have hm := integral_finite_jump_measure P atom ha m hmmeas (fun _ _ => le_max_right _ _)
    J hms K hmb H hH B hB hHb
  have hpi : Integrable (fun ω => ∑ n ∈ J ω, p n ω * H (atom n ω)) P :=
    bounded_signed_atomic_sum_integrable P atom ha p hpmeas J hps K
      (by
        filter_upwards [hpb] with ω hω
        have heq : (∑ n ∈ J ω, |p n ω|) = ∑ n ∈ J ω, p n ω := by
          apply Finset.sum_congr rfl
          intro n _
          exact abs_of_nonneg (le_max_right _ 0)
        rwa [heq]) H hH B hB hHb
  have hmi : Integrable (fun ω => ∑ n ∈ J ω, m n ω * H (atom n ω)) P :=
    bounded_signed_atomic_sum_integrable P atom ha m hmmeas J hms K
      (by
        filter_upwards [hmb] with ω hω
        have heq : (∑ n ∈ J ω, |m n ω|) = ∑ n ∈ J ω, m n ω := by
          apply Finset.sum_congr rfl
          intro n _
          exact abs_of_nonneg (le_max_right _ 0)
        rwa [heq]) H hH B hB hHb
  have hsum : ∀ ω, (∑ n ∈ J ω, d n ω * H (atom n ω)) =
      (∑ n ∈ J ω, p n ω * H (atom n ω)) - ∑ n ∈ J ω, m n ω * H (atom n ω) := by
    intro ω
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← sub_mul]
    congr 1
    by_cases h : 0 ≤ d n ω
    · simp only [p, m, max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · have hn : d n ω ≤ 0 := le_of_not_ge h
      simp only [p, m, max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), zero_sub, neg_neg]
  simp_rw [hsum]
  rw [integral_sub hpi hmi, hp, hm]

/-- Balanced positive and negative measures give zero mean for every bounded
measurable integrand against the signed pathwise sum. -/
theorem bounded_signed_atomic_sum_zero_of_balance
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (ha : ∀ n, Measurable (atom n))
    (d : ℕ → Ω → ℝ) (hd : ∀ n, Measurable (d n))
    (J : Ω → Finset ℕ) (hsupport : ∀ ω n, n ∉ J ω → d n ω = 0)
    (K : ℝ) (hmass : ∀ᵐ ω ∂P, (∑ n ∈ J ω, |d n ω|) ≤ K)
    (hbalance : jumpMeasure P atom (fun n ω => ENNReal.ofReal (max (d n ω) 0)) =
      jumpMeasure P atom (fun n ω => ENNReal.ofReal (max (-d n ω) 0)))
    (H : α → ℝ) (hH : Measurable H) (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ x, |H x| ≤ B) :
    (∫ ω, ∑ n ∈ J ω, d n ω * H (atom n ω) ∂P) = 0 := by
  have h := atomic_integral_signed_decomposition P atom ha d hd J hsupport K hmass H hH B hB hHb
  rw [hbalance, sub_self] at h
  exact h.symm

#print axioms atomic_integral_signed_decomposition
#print axioms bounded_signed_atomic_sum_zero_of_balance
end FTDAP
