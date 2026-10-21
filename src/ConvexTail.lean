import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
open Set Filter
open scoped Topology
namespace FTDAP

/-- B.2.1: convergence of lower and upper norm bounds gives the entire Cauchy step. -/
theorem convex_tail_cauchy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : ℕ → H) (a b : ℕ → ℝ) (A : ℝ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 A))
    (ha0 : ∀ N, 0 ≤ a N) (_hb0 : ∀ N, 0 ≤ b N)
    (hupper : ∀ n N, N ≤ n → ‖g n‖ ≤ b N)
    (hlower : ∀ n m N, N ≤ n → N ≤ m → 2 * a N ≤ ‖g n + g m‖) :
    CauchySeq g := by
  rw [cauchySeq_iff_le_tendsto_0]
  refine ⟨fun N => Real.sqrt (4 * (b N)^2 - 4 * (a N)^2),
    fun N => Real.sqrt_nonneg _, ?_, ?_⟩
  · intro n m N hn hm
    have hu := hupper n N hn
    have hv := hupper m N hm
    have hl := hlower n m N hn hm
    have hpar := parallelogram_law_with_norm ℝ (g n) (g m)
    have hs : 4 * (a N)^2 ≤ ‖g n + g m‖^2 := by
      nlinarith [sq_nonneg (‖g n + g m‖ - 2 * a N), norm_nonneg (g n + g m), ha0 N]
    have hu2 : ‖g n‖^2 ≤ (b N)^2 := by nlinarith [norm_nonneg (g n), _hb0 N]
    have hv2 : ‖g m‖^2 ≤ (b N)^2 := by nlinarith [norm_nonneg (g m), _hb0 N]
    rw [dist_eq_norm]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  · have ht := (((tendsto_const_nhds (x := (4 : ℝ))).mul (hb.pow 2)).sub
      ((tendsto_const_nhds (x := (4 : ℝ))).mul (ha.pow 2))).sqrt
    simpa using ht

/-- B.2.1: existence of a Cauchy selection from nested, nonempty convex sets
with uniformly bounded norm infima. No completeness assumption on H. -/
theorem nested_convex_cauchy_selection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : ℕ → Set H) (hne : ∀ n, (C n).Nonempty)
    (hconv : ∀ n, Convex ℝ (C n)) (hnested : Antitone C)
    (R : ℝ) (hbound : ∀ n, ∃ x ∈ C n, ‖x‖ ≤ R) :
    ∃ g : ℕ → H, (∀ n, g n ∈ C n) ∧ CauchySeq g := by
  classical
  let a : ℕ → ℝ := fun n => sInf (norm '' C n)
  have hne' : ∀ n, (norm '' C n).Nonempty := fun n => (hne n).image _
  have hbelow : ∀ n, BddBelow (norm '' C n) :=
    fun n => ⟨0, by rintro y ⟨x, hx, rfl⟩; exact norm_nonneg x⟩
  have ha0 : ∀ n, 0 ≤ a n := fun n => le_csInf (hne' n) (by
    rintro y ⟨x, hx, rfl⟩; exact norm_nonneg x)
  have ha_le : ∀ n x, x ∈ C n → a n ≤ ‖x‖ :=
    fun n x hx => csInf_le (hbelow n) ⟨x, hx, rfl⟩
  have hmono : Monotone a := by
    intro n m hnm
    exact le_csInf (hne' m) (by
      rintro y ⟨x, hx, rfl⟩
      exact ha_le n x (hnested hnm hx))
  have habove : BddAbove (range a) := by
    refine ⟨R, ?_⟩
    rintro y ⟨n, rfl⟩
    obtain ⟨x, hx, hRx⟩ := hbound n
    exact (ha_le n x hx).trans hRx
  let A := sSup (range a)
  have haA : ∀ n, a n ≤ A := fun n => le_csSup habove ⟨n, rfl⟩
  have hA0 : 0 ≤ A := (ha0 0).trans (haA 0)
  have hat : Tendsto a atTop (𝓝 A) := tendsto_atTop_ciSup hmono habove
  have hchoose : ∀ n : ℕ, ∃ x ∈ C n, ‖x‖ < A + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt : a n < A + 1 / ((n : ℝ) + 1) :=
      lt_add_of_le_of_pos (haA n) (by positivity)
    obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := exists_lt_of_csInf_lt (hne' n) hlt
    exact ⟨x, hx, hy⟩
  choose g hg hgn using hchoose
  refine ⟨g, hg, convex_tail_cauchy g a (fun n => A + 1 / ((n : ℝ) + 1)) A
    hat ?_ ha0 (fun n => by positivity) ?_ ?_⟩
  · simpa using (tendsto_const_nhds (x := A)).add tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n N hn
    apply (hgn n).le.trans
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · intro n m N hn hm
    have hmid : (1 / 2 : ℝ) • g n + (1 / 2 : ℝ) • g m ∈ C N :=
      hconv N (hnested hn (hg n)) (hnested hm (hg m)) (by norm_num)
        (by norm_num) (by norm_num)
    have h := ha_le N _ hmid
    rw [← smul_add, norm_smul] at h
    norm_num at h
    linarith

/-- The original bounded-sequence convex-tail lemma, with its original hypotheses. -/
theorem convex_tail_selection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : ℕ → H) (R : ℝ) (hf : ∀ n, ‖f n‖ ≤ R) :
    ∃ g : ℕ → H, (∀ n, g n ∈ convexHull ℝ (f '' Set.Ici n)) ∧ CauchySeq g := by
  refine nested_convex_cauchy_selection (fun n => convexHull ℝ (f '' Set.Ici n)) ?_ ?_ ?_ R ?_
  · intro n
    exact ⟨f n, subset_convexHull ℝ _ ⟨n, Set.mem_Ici.mpr le_rfl, rfl⟩⟩
  · intro n
    exact convex_convexHull ℝ _
  · intro n m hnm
    exact convexHull_mono (Set.image_mono (Set.Ici_subset_Ici.mpr hnm))
  · intro n
    exact ⟨f n, subset_convexHull ℝ _ ⟨n, Set.mem_Ici.mpr le_rfl, rfl⟩, hf n⟩
/-- The exact squared-norm estimate printed in Appendix A.1. -/
theorem printed_parallelogram_estimate {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : H) (m mn ei ej : ℝ)
    (hx : ‖x‖ ^ 2 ≤ m + ei) (hy : ‖y‖ ^ 2 ≤ m + ej)
    (hmid : mn ≤ ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2) :
    ‖x - y‖ ^ 2 ≤ 4 * (m - mn) + 2 * ei + 2 * ej := by
  have hp := parallelogram_law_with_norm ℝ x y
  have hn : ‖(1 / 2 : ℝ) • (x + y)‖ = (1 / 2 : ℝ) * ‖x + y‖ := by
    rw [norm_smul]
    norm_num
  rw [hn] at hmid
  nlinarith

/-- Appendix A.1: finite forward convex combinations converge in a complete Hilbert space. -/
theorem komlos_L2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : ℕ → H) (R : ℝ) (hf : ∀ n, ‖f n‖ ≤ R) :
    ∃ (g : ℕ → H) (Y : H),
      (∀ n, g n ∈ convexHull ℝ (f '' Set.Ici n)) ∧ Tendsto g atTop (𝓝 Y) := by
  obtain ⟨g, hg, hc⟩ := convex_tail_selection f R hf
  obtain ⟨Y, hY⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨g, Y, hg, hY⟩

#print axioms komlos_L2
end FTDAP
