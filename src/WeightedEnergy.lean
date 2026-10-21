import MeasureSteps
import WeightedPortfolioL2

open MeasureTheory
open scoped ENNReal
namespace FTDAP

/-- The reduced portfolio has uniformly bounded energy for each finite path. -/
theorem finite_weighted_energy {V : Type*} [NormedAddCommGroup V]
    (s : Finset ℕ) (G : ℕ → V) (c v : ℕ → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hc : ∀ k ∈ s, 0 < c k)
    (hv : ∀ k ∈ s, 0 ≤ v k)
    (hG : ∀ k ∈ s, ‖G k‖ ≤ c k * R)
    (hvariation : ∑ k ∈ s, v k ≤ R - 1) :
    (∑ k ∈ s, v k * (‖G k‖ ^ 2 / (c k ^ 2 * R ^ 3))) ≤ 1 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ ∑ k ∈ s, v k * (1 / R) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (weighted_L2_density_bound (G k) (c k) R (hc k hk) hRp (hG k hk))
        (hv k hk)
    _ = (∑ k ∈ s, v k) / R := by rw [← Finset.sum_mul]; ring
    _ ≤ (R - 1) / R := div_le_div_of_nonneg_right hvariation hRp.le
    _ ≤ 1 := (div_le_one hRp).mpr (by linarith)

/-- The product envelope is monotone along the ordered list of actual jumps. -/
theorem pathwise_product_monotone (R q : ℕ → ℝ) (hR0 : R 0 = 1)
    (hR : ∀ n, R (n+1) = R n * (1 + q n)) (hq : ∀ n, 0 ≤ q n) :
    Monotone R := by
  apply monotone_nat_of_le_succ
  intro n
  have hn := (sum_le_product_minus_one R q hR0 hR hq n).1
  rw [hR n]
  nlinarith [hq n]

/-- The wealth bound supplies the terminal product envelope at every jump. -/
theorem reduced_portfolio_terminal_envelope {V : Type*} [NormedAddCommGroup V]
    (G : ℕ → V) (c X R q : ℕ → ℝ) (N : ℕ)
    (hX0 : X 0 = 0) (hR0 : R 0 = 1)
    (hR : ∀ n, R (n+1) = R n * (1 + q n)) (hq : ∀ n, 0 ≤ q n)
    (hW : ∀ n, 0 ≤ 1 + X n)
    (hinc : ∀ n, |X (n+1) - X n| ≤ (1 + X n) * q n)
    (hc : ∀ k < N, 0 ≤ c k)
    (hG : ∀ k < N, ‖G k‖ ≤ c k * (1 + X k)) :
    ∀ k < N, ‖G k‖ ≤ c k * R N := by
  intro k hk
  have hb := (pathwise_product_bound 1 zero_le_one X R q hX0 hR0 hR hq hW hinc k).1
  simp only [one_mul] at hb
  have hm := pathwise_product_monotone R q hR0 hR hq (Nat.le_of_lt hk)
  exact (hG k hk).trans (mul_le_mul_of_nonneg_left (hb.trans hm) (hc k hk))

/-- The source product bounds total price variation, even when the coefficient varies. -/
theorem price_variation_le_product (c v R : ℕ → ℝ)
    (hc : ∀ n, 1 ≤ c n) (hv : ∀ n, 0 ≤ v n)
    (hR0 : R 0 = 1) (hR : ∀ n, R (n+1) = R n * (1 + c n * v n)) :
    ∀ N, (∑ k ∈ Finset.range N, v k) ≤ R N - 1 := by
  intro N
  have hb := (sum_le_product_minus_one R (fun n => c n * v n)
    hR0 hR (fun n => mul_nonneg (le_trans zero_le_one (hc n)) (hv n)) N).2
  apply le_trans _ hb
  apply Finset.sum_le_sum
  intro k _
  simpa using mul_le_mul_of_nonneg_right (hc k) (hv k)

/-- The exact nonnegative-real form used by the atomic measure construction. -/
theorem finite_weighted_energy_ennreal {V : Type*} [NormedAddCommGroup V]
    (s : Finset ℕ) (G : ℕ → V) (c v : ℕ → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hc : ∀ k ∈ s, 0 < c k)
    (hv : ∀ k ∈ s, 0 ≤ v k)
    (hG : ∀ k ∈ s, ‖G k‖ ≤ c k * R)
    (hvariation : ∑ k ∈ s, v k ≤ R - 1) :
    (∑ k ∈ s, ENNReal.ofReal (v k / (c k ^ 2 * R ^ 3)) *
      ENNReal.ofReal (‖G k‖ ^ 2)) ≤ 1 := by
  have hn : ∀ k ∈ s, 0 ≤ v k * (‖G k‖ ^ 2 / (c k ^ 2 * R ^ 3)) := by
    intro k hk
    exact mul_nonneg (hv k hk) (div_nonneg (sq_nonneg _) (by positivity))
  have he : (∑ k ∈ s, ENNReal.ofReal (v k / (c k ^ 2 * R ^ 3)) *
      ENNReal.ofReal (‖G k‖ ^ 2)) =
      ENNReal.ofReal (∑ k ∈ s, v k * (‖G k‖ ^ 2 / (c k ^ 2 * R ^ 3))) := by
    rw [ENNReal.ofReal_sum_of_nonneg hn]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← ENNReal.ofReal_mul (div_nonneg (hv k hk) (by positivity))]
    congr 1
    ring
  rw [he]
  exact_mod_cast ENNReal.ofReal_le_ofReal
    (finite_weighted_energy s G c v R hR hc hv hG hvariation)

/-- Finite path energy gives a uniform Hilbert bound without an assumed L2 estimate. -/
theorem finite_path_portfolio_L2 {Ω α V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (H : α → V) (hH : Measurable H)
    (jumps : Ω → Finset ℕ) (c v : ℕ → Ω → ℝ) (R : Ω → ℝ)
    (hpath : ∀ᵐ ω ∂P, 1 ≤ R ω ∧
      (∀ k ∈ jumps ω, 0 < c k ω ∧ 0 ≤ v k ω ∧
        ‖H (atom k ω)‖ ≤ c k ω * R ω ∧
        weight k ω = ENNReal.ofReal (v k ω / (c k ω ^ 2 * R ω ^ 3))) ∧
      (∀ k, k ∉ jumps ω → weight k ω = 0) ∧
      (∑ k ∈ jumps ω, v k ω) ≤ R ω - 1) :
    ∃ hL : MemLp H 2 (jumpMeasure P atom weight), ‖hL.toLp H‖ ≤ 1 := by
  have he : ∀ᵐ ω ∂P,
      ∑' n, weight n ω * ENNReal.ofReal (‖H (atom n ω)‖ ^ 2) ≤ 1 := by
    filter_upwards [hpath] with ω hω
    rw [tsum_eq_sum (s := jumps ω) (fun k hk => by rw [hω.2.2.1 k hk, zero_mul])]
    have he := finite_weighted_energy_ennreal (jumps ω) (fun k => H (atom k ω))
      (fun k => c k ω) (fun k => v k ω) (R ω) hω.1
      (fun k hk => (hω.2.1 k hk).1)
      (fun k hk => (hω.2.1 k hk).2.1)
      (fun k hk => (hω.2.1 k hk).2.2.1) hω.2.2.2
    convert he using 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [(hω.2.1 k hk).2.2.2]
  let hL := weighted_portfolio_memLp P atom weight ha hw H hH 1 (by simp) he
  refine ⟨hL, ?_⟩
  have hb := weighted_portfolio_lp_norm_bound P atom weight ha hw H hH 1 (by simp) he
  simp only [ENNReal.toReal_one] at hb
  nlinarith [norm_nonneg (hL.toLp H)]

/-- The ordered finite-jump product estimate implies the unit-admissible L2 bound. -/
theorem ordered_product_portfolio_L2 {Ω α V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (atom : ℕ → Ω → α) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (H : α → V) (hH : Measurable H) (N : Ω → ℕ)
    (c v X R : ℕ → Ω → ℝ)
    (hpath : ∀ᵐ ω ∂P,
      X 0 ω = 0 ∧ R 0 ω = 1 ∧
      (∀ n, R (n+1) ω = R n ω * (1 + c n ω * v n ω)) ∧
      (∀ n, 1 ≤ c n ω) ∧ (∀ n, 0 ≤ v n ω) ∧
      (∀ n, 0 ≤ 1 + X n ω) ∧
      (∀ n, |X (n+1) ω - X n ω| ≤ (1 + X n ω) * (c n ω * v n ω)) ∧
      (∀ k < N ω, ‖H (atom k ω)‖ ≤ c k ω * (1 + X k ω)) ∧
      (∀ k < N ω, weight k ω =
        ENNReal.ofReal (v k ω / (c k ω ^ 2 * R (N ω) ω ^ 3))) ∧
      (∀ k, N ω ≤ k → weight k ω = 0)) :
    ∃ hL : MemLp H 2 (jumpMeasure P atom weight), ‖hL.toLp H‖ ≤ 1 := by
  apply finite_path_portfolio_L2 P atom weight ha hw H hH
    (fun ω => Finset.range (N ω)) c v (fun ω => R (N ω) ω)
  filter_upwards [hpath] with ω hω
  obtain ⟨hX0, hR0, hR, hc, hv, hW, hinc, hG, hweight, hzero⟩ := hω
  have hq : ∀ n, 0 ≤ c n ω * v n ω := fun n =>
    mul_nonneg (le_trans zero_le_one (hc n)) (hv n)
  have hbound := reduced_portfolio_terminal_envelope (fun k => H (atom k ω))
    (fun k => c k ω) (fun k => X k ω) (fun k => R k ω)
    (fun k => c k ω * v k ω) (N ω) hX0 hR0 hR hq hW hinc
    (fun k _ => le_trans zero_le_one (hc k)) hG
  refine ⟨(sum_le_product_minus_one (fun k => R k ω)
    (fun k => c k ω * v k ω) hR0 hR hq (N ω)).1, ?_, ?_, ?_⟩
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    exact ⟨lt_of_lt_of_le zero_lt_one (hc k), hv k, hbound k hk', hweight k hk'⟩
  · intro k hk
    exact hzero k (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h)))
  · exact price_variation_le_product (fun k => c k ω) (fun k => v k ω)
      (fun k => R k ω) hc hv hR0 hR (N ω)

#print axioms ordered_product_portfolio_L2
#print axioms price_variation_le_product
#print axioms pathwise_product_monotone
#print axioms reduced_portfolio_terminal_envelope
#print axioms finite_path_portfolio_L2
#print axioms finite_weighted_energy
#print axioms finite_weighted_energy_ennreal
end FTDAP
