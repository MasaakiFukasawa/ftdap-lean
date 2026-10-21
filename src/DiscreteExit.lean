import CadlagDiscrete
import ContinuousHitting

open Set Filter TopologicalSpace
open scoped Topology
namespace FTDAP
variable {V : Type*} [TopologicalSpace V] [DiscreteTopology V]

/-- Right continuity into discrete states gives a nonempty interval of constancy. -/
theorem discrete_right_constant_interval (f : ℝ → V)
    (hf : IsRightContinuous f) (t : ℝ) :
    ∃ u > t, ∀ s ∈ Ico t u, f s = f t := by
  have he : {s | f s = f t} ∈ 𝓝[>] t :=
    (hf t) ((isOpen_discrete ({f t} : Set V)).mem_nhds (mem_singleton _))
  obtain ⟨u, htu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (lt_add_one t)).mp he
  refine ⟨u, htu, ?_⟩
  intro s hs
  rcases hs.1.eq_or_lt with h | h
  · rw [← h]
  · exact hu ⟨h, hs.2⟩

/-- The first departure from the current discrete state occurs strictly later
and is attained. There can be no departure hidden immediately after its infimum. -/
theorem discrete_first_exit_attained (f : ℝ → V) (hf : IsRightContinuous f)
    (t : ℝ) (hex : ∃ s, t ≤ s ∧ f s ≠ f t) :
    t < sInf {s | t ≤ s ∧ f s ≠ f t} ∧
      f (sInf {s | t ≤ s ∧ f s ≠ f t}) ≠ f t ∧
      ∀ s, t ≤ s → s < sInf {s | t ≤ s ∧ f s ≠ f t} → f s = f t := by
  let A : Set ℝ := {s | t ≤ s ∧ f s ≠ f t}
  have hA : A.Nonempty := hex
  have hb : BddBelow A := ⟨t, fun s hs => hs.1⟩
  have hbefore : ∀ s, t ≤ s → s < sInf A → f s = f t := by
    intro s hts hs
    by_contra hne
    exact (not_lt_of_ge (csInf_le hb ⟨hts, hne⟩)) hs
  obtain ⟨u, htu, hu⟩ := discrete_right_constant_interval f hf t
  have huA : u ≤ sInf A := by
    apply le_csInf hA
    intro s hs
    by_contra h
    exact hs.2 (hu s ⟨hs.1, lt_of_not_ge h⟩)
  have ht : t < sInf A := htu.trans_le huA
  refine ⟨ht, ?_, hbefore⟩
  intro heq
  obtain ⟨v, htv, hv⟩ := discrete_right_constant_interval f hf (sInf A)
  have hvA : v ≤ sInf A := by
    apply le_csInf hA
    intro s hs
    have hτs : sInf A ≤ s := csInf_le hb hs
    by_contra h
    exact hs.2 ((hv s ⟨hτs, lt_of_not_ge h⟩).trans heq)
  exact (not_lt_of_ge hvA) htv

end FTDAP

namespace FTDAP
variable {V : Type*} [TopologicalSpace V] [T1Space V]

/-- A finite path range supplies the discrete topology needed for exit attainment. -/
theorem finite_range_first_exit_attained (f : ℝ → V) (hf : IsRightContinuous f)
    (hfinite : (Set.range f).Finite) (t : ℝ)
    (hex : ∃ s, t ≤ s ∧ f s ≠ f t) :
    t < sInf {s | t ≤ s ∧ f s ≠ f t} ∧
      f (sInf {s | t ≤ s ∧ f s ≠ f t}) ≠ f t ∧
      ∀ s, t ≤ s → s < sInf {s | t ≤ s ∧ f s ≠ f t} → f s = f t := by
  let : DiscreteTopology (Set.range f) := isDiscrete_iff_discreteTopology.mp hfinite.isDiscrete
  let g : ℝ → Set.range f := fun s => ⟨f s, Set.mem_range_self s⟩
  have hg : IsRightContinuous g := fun s => tendsto_subtype_rng.mpr (hf s)
  have he : ∃ s, t ≤ s ∧ g s ≠ g t := by
    obtain ⟨s, hts, hne⟩ := hex
    exact ⟨s, hts, fun h => hne (congrArg Subtype.val h)⟩
  have h := discrete_first_exit_attained g hg t he
  have hi : ∀ a b, g a = g b ↔ f a = f b := fun a b =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  simpa only [ne_eq, hi] using h

/-- Each attained first departure is an actual discontinuity, not an extra
observation time at which the state has stayed unchanged. -/
theorem finite_range_exit_is_jump [T2Space V] (f : ℝ → V) (hf : IsRightContinuous f)
    (hfinite : (Set.range f).Finite) (t : ℝ)
    (hex : ∃ s, t ≤ s ∧ f s ≠ f t) :
    ¬ ContinuousAt f (sInf {s | t ≤ s ∧ f s ≠ f t}) := by
  obtain ⟨ht, hne, hbefore⟩ := finite_range_first_exit_attained f hf hfinite t hex
  let τ := sInf {s | t ≤ s ∧ f s ≠ f t}
  have he : ∀ᶠ s in 𝓝[<] τ, f s = f t := by
    have hl : ∀ᶠ s in 𝓝[<] τ, t < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)
    have hr : ∀ᶠ s in 𝓝[<] τ, s < τ := self_mem_nhdsWithin
    filter_upwards [hl, hr] with s hts hsτ
    exact hbefore s hts.le hsτ
  have hlim : Tendsto f (𝓝[<] τ) (𝓝 (f t)) := by
    apply (tendsto_const_nhds (x := f t)).congr'
    filter_upwards [he] with s hs using hs.symm
  intro hc
  have hτlim : Tendsto f (𝓝[<] τ) (𝓝 (f τ)) := hc.mono_left nhdsWithin_le_nhds
  exact hne (tendsto_nhds_unique hτlim hlim)

#print axioms finite_range_exit_is_jump
#print axioms finite_range_first_exit_attained
#print axioms discrete_right_constant_interval
#print axioms discrete_first_exit_attained
end FTDAP
