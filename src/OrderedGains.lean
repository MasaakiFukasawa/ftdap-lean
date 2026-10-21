import AdmissibleReduction
import WeightedEnergy

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal
namespace FTDAP
variable {ι V : Type*} [LinearOrder ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
attribute [local instance] Classical.propDecidable

/-- For an ordered enumeration, the gain immediately before jump k is its prefix sum. -/
theorem ordered_pre_gain (N k : ℕ) (hk : k < N) (τ : ℕ → ι)
    (horder : ∀ j l, j < l → l < N → τ j < τ l)
    (Δ H : ℕ → V) :
    (∑ j ∈ Finset.range N, if τ j < τ k then ⟪H j, Δ j⟫ else 0) =
      ∑ j ∈ Finset.range k, ⟪H j, Δ j⟫ := by
  have he : ∀ j < N, τ j < τ k ↔ j < k := by
    intro j hj
    constructor
    · intro h
      by_contra hn
      have hkj : k ≤ j := Nat.le_of_not_gt hn
      rcases hkj.eq_or_lt with hkj | hkj
      · subst j
        exact lt_irrefl _ h
      · exact (not_lt_of_ge (horder k j hkj hj).le) h
    · intro h
      exact horder j k h hk
  calc
    _ = ∑ j ∈ Finset.range N, if j ∈ Finset.range k then ⟪H j, Δ j⟫ else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j (Finset.mem_range.mp hj)]
      simp only [Finset.mem_range]
      split_ifs <;> rfl
    _ = ∑ j ∈ Finset.range k, ⟪H j, Δ j⟫ := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_iff_right_of_imp (fun h => h.trans hk)

/-- The finite prefix sums satisfy the exact single-jump recurrence. -/
theorem ordered_gain_recurrence (N : ℕ) (H Δ : ℕ → V) (n : ℕ) :
    (∑ k ∈ Finset.range (min (n+1) N), ⟪H k, Δ k⟫) -
      (∑ k ∈ Finset.range (min n N), ⟪H k, Δ k⟫) =
      if n < N then ⟪H n, Δ n⟫ else 0 := by
  by_cases hn : n < N
  · rw [min_eq_left (Nat.succ_le_of_lt hn), min_eq_left hn.le, Finset.sum_range_succ,
      ite_eq_left hn]
    ring
  · have hNn := Nat.le_of_not_gt hn
    rw [min_eq_right (hNn.trans (Nat.le_succ n)), min_eq_right hNn, ite_eq_right hn]
    simp

/-- The terminal product is built directly from the ordered increments. -/
theorem ordered_product_recurrence (N : ℕ) (q : ℕ → ℝ) (n : ℕ) :
    (∏ k ∈ Finset.range (min (n+1) N), (1 + q k)) =
      (∏ k ∈ Finset.range (min n N), (1 + q k)) *
        (1 + if n < N then q n else 0) := by
  by_cases hn : n < N
  · rw [min_eq_left (Nat.succ_le_of_lt hn), min_eq_left hn.le,
      Finset.prod_range_succ, ite_eq_left hn]
  · have hNn := Nat.le_of_not_gt hn
    rw [min_eq_right (hNn.trans (Nat.le_succ n)), min_eq_right hNn, ite_eq_right hn]
    simp

/-- The reduced portfolio norm bound controls every actual gain increment. -/
theorem reduced_gain_increment_bound (N : ℕ) (H Δ : ℕ → V) (c X : ℕ → ℝ)
    (hX : ∀ n, X n = ∑ k ∈ Finset.range (min n N), ⟪H k, Δ k⟫)
    (hG : ∀ n < N, ‖H n‖ ≤ c n * (1 + X n)) :
    ∀ n, |X (n+1) - X n| ≤ (1 + X n) *
      (if n < N then c n * ‖Δ n‖ else 0) := by
  intro n
  rw [hX (n+1), hX n, ordered_gain_recurrence]
  by_cases hn : n < N
  · rw [ite_eq_left hn, ite_eq_left hn]
    have hb := (abs_real_inner_le_norm (H n) (Δ n)).trans
      (mul_le_mul_of_nonneg_right (hG n hn) (norm_nonneg (Δ n)))
    rw [mul_assoc, mul_left_comm (c n) (1 + X n)] at hb
    rwa [← hX n]
  · rw [ite_eq_right hn, ite_eq_right hn]
    simp

/-- The energy estimate is obtained directly from finite prefix gains and the
finite product, with both recurrences proved from those formulas. -/
theorem ordered_unit_portfolio_energy (N : ℕ) (H Δ : ℕ → V) (c : ℕ → ℝ)
    (hc : ∀ n, 1 ≤ c n)
    (hadm : ∀ n ≤ N, 0 ≤ 1 + ∑ k ∈ Finset.range n, ⟪H k, Δ k⟫)
    (hG : ∀ n < N, ‖H n‖ ≤ c n * (1 + ∑ k ∈ Finset.range n, ⟪H k, Δ k⟫)) :
    let R := ∏ k ∈ Finset.range N, (1 + c k * ‖Δ k‖)
    (∑ k ∈ Finset.range N, ENNReal.ofReal (‖Δ k‖ / (c k ^ 2 * R ^ 3)) *
      ENNReal.ofReal (‖H k‖ ^ 2)) ≤ 1 := by
  let X : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (min n N), ⟪H k, Δ k⟫
  let R : ℕ → ℝ := fun n => ∏ k ∈ Finset.range (min n N), (1 + c k * ‖Δ k‖)
  let q : ℕ → ℝ := fun n => if n < N then c n * ‖Δ n‖ else 0
  have hX0 : X 0 = 0 := by simp [X]
  have hR0 : R 0 = 1 := by simp [R]
  have hR : ∀ n, R (n+1) = R n * (1 + q n) :=
    fun n => ordered_product_recurrence N (fun k => c k * ‖Δ k‖) n
  have hq : ∀ n, 0 ≤ q n := by
    intro n
    dsimp [q]
    split_ifs
    · exact mul_nonneg (le_trans zero_le_one (hc n)) (norm_nonneg _)
    · exact le_rfl
  have hW : ∀ n, 0 ≤ 1 + X n := fun n => hadm (min n N) (min_le_right _ _)
  have hGn : ∀ n < N, ‖H n‖ ≤ c n * (1 + X n) := by
    intro n hn
    simpa only [X, min_eq_left hn.le] using hG n hn
  have hinc := reduced_gain_increment_bound N H Δ c X (fun _ => rfl) hGn
  have henv := reduced_portfolio_terminal_envelope H c X R q N hX0 hR0 hR hq hW hinc
    (fun n _ => le_trans zero_le_one (hc n)) hGn
  have hprod := sum_le_product_minus_one R q hR0 hR hq N
  have hv : (∑ k ∈ Finset.range N, ‖Δ k‖) ≤ R N - 1 := by
    apply le_trans _ hprod.2
    apply Finset.sum_le_sum
    intro k hk
    dsimp [q]
    rw [ite_eq_left (Finset.mem_range.mp hk)]
    simpa using mul_le_mul_of_nonneg_right (hc k) (norm_nonneg (Δ k))
  have he := finite_weighted_energy_ennreal (Finset.range N) H c (fun k => ‖Δ k‖)
    (R N) hprod.1 (fun k _ => lt_of_lt_of_le zero_lt_one (hc k))
    (fun k _ => norm_nonneg _) (fun k hk => henv k (Finset.mem_range.mp hk)) hv
  simpa only [R, min_self] using he

#print axioms ordered_unit_portfolio_energy
#print axioms ordered_pre_gain
#print axioms ordered_gain_recurrence
#print axioms ordered_product_recurrence
#print axioms reduced_gain_increment_bound
end FTDAP
