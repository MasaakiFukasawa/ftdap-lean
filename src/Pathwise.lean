import Geometry
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology RealInnerProductSpace
namespace FTDAP
set_option linter.unusedSectionVars false

/-- The product wealth bound and variation bound, for every finite list of jumps. -/
theorem pathwise_product_bound (a : ℝ) (_ha : 0 ≤ a) (X R q : ℕ → ℝ)
    (hX0 : X 0 = 0) (hR0 : R 0 = 1)
    (hR : ∀ n, R (n+1) = R n * (1 + q n))
    (hq : ∀ n, 0 ≤ q n) (_hW : ∀ n, 0 ≤ a + X n)
    (hinc : ∀ n, |X (n+1) - X n| ≤ (a + X n) * q n) :
    ∀ n, a + X n ≤ a * R n ∧
      (∑ k ∈ Finset.range n, |X (k+1) - X k|) ≤ a * (R n - 1) := by
  intro n
  induction n with
  | zero => simp [hX0, hR0]
  | succ n ih =>
    have hd := (le_abs_self (X (n+1) - X n)).trans (hinc n)
    have hb := mul_le_mul_of_nonneg_right ih.1 (by linarith [hq n] : 0 ≤ 1 + q n)
    have hv := (hinc n).trans (mul_le_mul_of_nonneg_right ih.1 (hq n))
    constructor
    · rw [hR n]
      nlinarith
    · rw [Finset.sum_range_succ, hR n]
      nlinarith [ih.2]

/-- With c ≥ 1 the product also bounds total price variation. -/
theorem sum_le_product_minus_one (R q : ℕ → ℝ) (hR0 : R 0 = 1)
    (hR : ∀ n, R (n+1) = R n * (1 + q n)) (hq : ∀ n, 0 ≤ q n) :
    ∀ n, 1 ≤ R n ∧ (∑ k ∈ Finset.range n, q k) ≤ R n - 1 := by
  intro n
  induction n with
  | zero => simp [hR0]
  | succ n ih =>
    rw [hR n, Finset.sum_range_succ]
    have hmul := mul_le_mul_of_nonneg_right ih.1 (hq n)
    constructor <;> nlinarith [ih.1, ih.2, hq n]

/-- The scalar last step of NA ⇒ NFLVR, with the common pathwise R fixed. -/
theorem terminal_squeeze (f ε : ℕ → ℝ) (limit R : ℝ)
    (hf : Tendsto f atTop (𝓝 limit)) (he : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, f n ≤ ε n * (R - 1)) (hn : 0 ≤ limit) : limit = 0 := by
  have ht : Tendsto (fun n => ε n * (R - 1)) atTop (𝓝 0) := by
    simpa using he.mul_const (R - 1)
  have hl : limit ≤ 0 := le_of_tendsto_of_tendsto hf ht (Eventually.of_forall hbound)
  exact le_antisymm hl hn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A uniform bound over all prefixes (indeed all subsets) of the finite jump set. -/
theorem finite_stieltjes_error {ι : Type*} (s p : Finset ι) (hp : p ⊆ s)
    (h g z : ι → H) :
    |∑ k ∈ p, ⟪h k - g k, z k⟫| ≤ ∑ k ∈ s, ‖h k - g k‖ * ‖z k‖ := by
  calc
    _ ≤ ∑ k ∈ p, |⟪h k - g k, z k⟫| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ p, ‖h k - g k‖ * ‖z k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_real_inner_le_norm _ _
    _ ≤ ∑ k ∈ s, ‖h k - g k‖ * ‖z k‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hp (by
        intro k hk hkp
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Pointwise convergence at finitely many jumps gives a common error tending to zero. -/
theorem finite_stieltjes_error_tendsto {ι : Type*} (s : Finset ι)
    (h : ℕ → ι → H) (g z : ι → H)
    (hh : ∀ k ∈ s, Tendsto (fun n => h n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑ k ∈ s, ‖h n k - g k‖ * ‖z k‖) atTop (𝓝 0) := by
  have ht : ∀ k ∈ s, Tendsto (fun n => ‖h n k - g k‖ * ‖z k‖) atTop (𝓝 0) := by
    intro k hk
    simpa using (((hh k hk).sub (tendsto_const_nhds (x := g k))).norm).mul_const ‖z k‖
  simpa using tendsto_finsetSum s ht

#print axioms pathwise_product_bound
#print axioms terminal_squeeze
#print axioms finite_stieltjes_error_tendsto
end FTDAP
