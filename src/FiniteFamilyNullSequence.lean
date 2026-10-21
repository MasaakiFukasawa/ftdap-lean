import WeakDualFiniteDetectors
import Mathlib.Data.Nat.Pairing

open Set Filter
open scoped Topology
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E]

/-- Enumerate a family of finite sets by pairing their level and list index;
invalid list indices contribute zero. -/
noncomputable def finiteFamilySequence (S : ℕ → Finset E) (k : ℕ) : E :=
  if h : (Nat.unpair k).2 < (S (Nat.unpair k).1).toList.length then
    (S (Nat.unpair k).1).toList[(Nat.unpair k).2] else 0

/-- Every element of every finite level occurs in the sequence. -/
theorem finiteFamilySequence_covers (S : ℕ → Finset E) (n : ℕ) (v : E) (hv : v ∈ S n) :
    ∃ k, finiteFamilySequence S k = v := by
  classical
  have hvl : v ∈ (S n).toList := by simpa using hv
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hvl
  refine ⟨Nat.pair n j, ?_⟩
  simpa only [finiteFamilySequence, Nat.unpair_pair, dite_eq_left hj] using he

/-- Shrinking finite levels give a unit-bounded null sequence covering all levels. -/
theorem finite_family_null_sequence (S : ℕ → Finset E)
    (hS : ∀ n v, v ∈ S n → ‖v‖ ≤ 1 / ((n : ℝ)+1)) :
    (∀ k, ‖finiteFamilySequence S k‖ ≤ 1) ∧
      Tendsto (finiteFamilySequence S) atTop (𝓝 0) := by
  classical
  have hm : ∀ k (hk : (Nat.unpair k).2 < (S (Nat.unpair k).1).toList.length),
      (S (Nat.unpair k).1).toList[(Nat.unpair k).2]'hk ∈ S (Nat.unpair k).1 := by
    intro k hk
    simpa only [Finset.mem_toList] using List.getElem_mem hk
  constructor
  · intro k
    unfold finiteFamilySequence
    split_ifs with hk
    · have hd : (1 : ℝ) / ((↑(Nat.unpair k).1 : ℝ)+1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.unpair k).1])
      exact (hS _ _ (hm k hk)).trans hd
    · simp
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hrec : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hrec) ε hε
    let bad : Finset ℕ := (Finset.range N).biUnion (fun n =>
      (Finset.range (S n).toList.length).image (Nat.pair n))
    refine ⟨bad.sup id + 1, ?_⟩
    intro k hk
    rw [dist_zero_right]
    unfold finiteFamilySequence
    split_ifs with hj
    · have hn : N ≤ (Nat.unpair k).1 := by
        by_contra hn
        have hmem : k ∈ bad := by
          apply Finset.mem_biUnion.mpr
          refine ⟨(Nat.unpair k).1, Finset.mem_range.mpr (Nat.lt_of_not_ge hn), ?_⟩
          exact Finset.mem_image.mpr ⟨(Nat.unpair k).2, Finset.mem_range.mpr hj, Nat.pair_unpair k⟩
        have hs : k ≤ bad.sup id := Finset.le_sup (f := id) hmem
        omega
      have hsmall := hN (Nat.unpair k).1 hn
      have hsmall' : 1 / ((↑(Nat.unpair k).1 : ℝ)+1) < ε := by
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / ((↑(Nat.unpair k).1 : ℝ)+1))] using hsmall
      exact (hS _ _ (hm k hj)).trans_lt hsmall'
    · simpa using hε

#print axioms finiteFamilySequence_covers
#print axioms finite_family_null_sequence
end FTDAP
