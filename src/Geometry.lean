import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set
open scoped RealInnerProductSpace
namespace FTDAP
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def NonnegOn (J : Finset H) (u : H) : Prop := ∀ z ∈ J, 0 ≤ ⟪u, z⟫

noncomputable def strictFace (J : Finset H) (u : H) : Finset H := by
  classical
  exact J.filter (fun z => 0 < ⟪u, z⟫)

noncomputable def zeroFace (J : Finset H) (u : H) : Finset H := by
  classical
  exact J.filter (fun z => ⟪u, z⟫ = 0)

/-- Maximality is over all feasible directions; positive normalization preserves this property. -/
theorem exists_maximal_separator (J : Finset H) :
    ∃ u : H, NonnegOn J u ∧
      ∀ v : H, NonnegOn J v → (strictFace J v).card ≤ (strictFace J u).card := by
  classical
  let supports := J.powerset.filter (fun A => ∃ u : H, NonnegOn J u ∧ strictFace J u = A)
  have hne : supports.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    refine ⟨0, ?_, ?_⟩
    · intro z hz
      simp
    · simp [strictFace]
  obtain ⟨A, hA, hmax⟩ := supports.exists_max_image Finset.card hne
  obtain ⟨u, hu, rfl⟩ := (Finset.mem_filter.mp hA).2
  refine ⟨u, hu, ?_⟩
  intro v hv
  apply hmax _
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), v, hv, rfl⟩

private theorem exists_small_positive {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, |b i| * ε < a i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨ε, hε, he⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    obtain ⟨δ, hδ, hd⟩ := exists_pos_mul_lt (ha i (Finset.mem_insert_self _ _)) |b i|
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg _)).trans_lt hd
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _)).trans_lt (he j hj)

/-- The perturbation argument in the vector portfolio lemma. -/
theorem maximal_zero_face (J : Finset H) (u : H) (hu : NonnegOn J u)
    (hmax : ∀ q : H, NonnegOn J q → (strictFace J q).card ≤ (strictFace J u).card)
    (v : H) (hv : NonnegOn (zeroFace J u) v) :
    ∀ z ∈ zeroFace J u, ⟪v, z⟫ = 0 := by
  classical
  intro z hz
  by_contra hzero
  have hzpos : 0 < ⟪v, z⟫ := lt_of_le_of_ne (hv z hz) (Ne.symm hzero)
  obtain ⟨ε, hε, he⟩ := exists_small_positive (strictFace J u)
    (fun y => ⟪u, y⟫) (fun y => ⟪v, y⟫)
    (by intro y hy; exact (Finset.mem_filter.mp hy).2)
  have hstrict : strictFace J u ⊆ strictFace J (u + ε • v) := by
    intro y hy
    have hyJ := (Finset.mem_filter.mp hy).1
    have hyε := he y hy
    have hn := neg_le_abs ⟪v, y⟫
    have hm := mul_le_mul_of_nonneg_right hn hε.le
    apply Finset.mem_filter.mpr
    refine ⟨hyJ, ?_⟩
    simp only [inner_add_left, real_inner_smul_left]
    nlinarith
  have hfeasible : NonnegOn J (u + ε • v) := by
    intro y hy
    by_cases h : ⟪u, y⟫ = 0
    · have hyv := hv y (Finset.mem_filter.mpr ⟨hy, h⟩)
      simp only [inner_add_left, real_inner_smul_left, h, zero_add]
      exact mul_nonneg hε.le hyv
    · have hyp : 0 < ⟪u, y⟫ := lt_of_le_of_ne (hu y hy) (Ne.symm h)
      exact (Finset.mem_filter.mp (hstrict (Finset.mem_filter.mpr ⟨hy, hyp⟩))).2.le
  have hznew : z ∈ strictFace J (u + ε • v) := by
    obtain ⟨hzJ, hzu⟩ := Finset.mem_filter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨hzJ, ?_⟩
    simp only [inner_add_left, real_inner_smul_left, hzu, zero_add]
    exact mul_pos hε hzpos
  have hzold : z ∉ strictFace J u := by
    have hzu := (Finset.mem_filter.mp hz).2
    simp [strictFace, hzu]
  have hss : strictFace J u ⊂ strictFace J (u + ε • v) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hstrict, by
      intro heq
      exact hzold (heq ▸ hznew)⟩
  exact (not_lt_of_ge (hmax _ hfeasible)) (Finset.card_lt_card hss)

/-- A nonnegative direction in the span of the zero face is zero. -/
theorem zero_face_no_nonzero_direction (J : Finset H) (u : H) (hu : NonnegOn J u)
    (hmax : ∀ q : H, NonnegOn J q → (strictFace J q).card ≤ (strictFace J u).card)
    (v : H) (hvspan : v ∈ Submodule.span ℝ (zeroFace J u : Set H))
    (hv : NonnegOn (zeroFace J u) v) : v = 0 := by
  have hz := maximal_zero_face J u hu hmax v hv
  have hall : ∀ x ∈ Submodule.span ℝ (zeroFace J u : Set H), ⟪v, x⟫ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hz x hx
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
    | smul a x hx ih => simp [inner_smul_right, ih]
  exact (inner_self_eq_zero).mp (hall v hvspan)

/-- Compactness upgrades pointwise absence of nonnegative directions to a uniform bound. -/
theorem finite_constraint_bound [FiniteDimensional ℝ H]
    (K : Submodule ℝ H) (J : Finset H)
    (hno : ∀ v : K, (∀ z ∈ J, 0 ≤ ⟪(v : H), z⟫) → v = 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (v : K) (w : ℝ), 0 ≤ w →
      (∀ z ∈ J, -w ≤ ⟪(v : H), z⟫) → ‖v‖ ≤ κ * w := by
  classical
  by_cases htriv : ∀ v : K, v = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro v w hw hv
    simpa [htriv v] using hw
  obtain ⟨v₀, hv₀⟩ := not_forall.mp htriv
  have hJ : J.Nonempty := by
    by_contra he
    have heq : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    exact hv₀ (hno v₀ (by simp [heq]))
  let F : K → ℝ := fun v => J.sup' hJ (fun z => -⟪(v : H), z⟫)
  have hF : Continuous F := by
    apply Continuous.finset_sup'_apply
    intro z hz
    exact (continuous_subtype_val.inner continuous_const).neg
  have hpositive : ∀ v : K, ‖v‖ = 1 → 0 < F v := by
    intro v hv
    by_contra hp
    have hn : ∀ z ∈ J, 0 ≤ ⟪(v : H), z⟫ := by
      intro z hz
      have hb : -⟪(v : H), z⟫ ≤ F v := Finset.le_sup' (fun z => -⟪(v : H), z⟫) hz
      have hnp := le_of_not_gt hp
      linarith
    have heq := hno v hn
    simp [heq] at hv
  have hne : (Metric.sphere (0 : K) 1).Nonempty := by
    refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
    simpa [Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hv₀
  obtain ⟨q, hq, hmin⟩ := (isCompact_sphere (0 : K) 1).exists_isMinOn hne hF.continuousOn
  have hqn : ‖q‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hq
  have hβ : 0 < F q := hpositive q hqn
  refine ⟨(F q)⁻¹, inv_pos.mpr hβ, ?_⟩
  intro v w hw hv
  by_cases hzero : v = 0
  · simp only [hzero, norm_zero]
    exact mul_nonneg (inv_pos.mpr hβ).le hw
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hzero
  let r : K := ‖v‖⁻¹ • v
  have hr : r ∈ Metric.sphere (0 : K) 1 := by
    simpa [r, Metric.mem_sphere, dist_zero_right] using norm_smul_inv_norm (𝕜 := ℝ) hzero
  have hlow : F q ≤ F r := hmin hr
  have hupp : F r ≤ ‖v‖⁻¹ * w := by
    apply (Finset.sup'_le_iff hJ _).mpr
    intro z hz
    change -⟪(‖v‖⁻¹ • (v : H)), z⟫ ≤ _
    rw [real_inner_smul_left]
    have hm := mul_le_mul_of_nonneg_left (neg_le_neg (hv z hz)) (inv_pos.mpr hn).le
    simpa only [mul_neg, neg_neg] using hm
  have hh : F q * ‖v‖ ≤ w := by
    have hm := mul_le_mul_of_nonneg_right (hlow.trans hupp) hn.le
    calc
      F q * ‖v‖ ≤ (‖v‖⁻¹ * w) * ‖v‖ := hm
      _ = w := by field_simp
  have hm := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hβ).le
  simpa [← mul_assoc, hβ.ne'] using hm

/-- Full deterministic projection step of the portfolio reduction. -/
theorem portfolio_projection_bound [FiniteDimensional ℝ H]
    (J : Finset H) (u : H) (hu : NonnegOn J u)
    (hmax : ∀ q : H, NonnegOn J q → (strictFace J q).card ≤ (strictFace J u).card) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (h : H) (w : ℝ), 0 ≤ w →
      (∀ z ∈ zeroFace J u, -w ≤ ⟪h, z⟫) →
      ‖(Submodule.span ℝ (zeroFace J u : Set H)).starProjection h‖ ≤ κ * w ∧
      ∀ z ∈ zeroFace J u,
        ⟪(Submodule.span ℝ (zeroFace J u : Set H)).starProjection h, z⟫ = ⟪h, z⟫ := by
  let K := Submodule.span ℝ (zeroFace J u : Set H)
  have hno : ∀ v : K, (∀ z ∈ zeroFace J u, 0 ≤ ⟪(v : H), z⟫) → v = 0 := by
    intro v hv
    apply Subtype.ext
    exact zero_face_no_nonzero_direction J u hu hmax (v : H) v.property hv
  obtain ⟨κ, hκ, hb⟩ := finite_constraint_bound K (zeroFace J u) hno
  have heq : ∀ h z, z ∈ zeroFace J u → ⟪K.starProjection h, z⟫ = ⟪h, z⟫ := by
    intro h z hz
    rw [K.inner_starProjection_left_eq_right]
    rw [K.starProjection_eq_self_iff.mpr (Submodule.subset_span hz)]
  refine ⟨κ, hκ, ?_⟩
  intro h w hw hh
  refine ⟨?_, heq h⟩
  exact hb ⟨K.starProjection h, K.starProjection_apply_mem h⟩ w hw (by
    intro z hz
    change -w ≤ ⟪K.starProjection h, z⟫
    rw [heq h z hz]
    exact hh z hz)

#print axioms exists_maximal_separator
#print axioms zero_face_no_nonzero_direction
#print axioms portfolio_projection_bound
end FTDAP
