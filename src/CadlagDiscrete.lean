import CadlagBase
import Mathlib.Topology.DiscreteSubset

open Set Filter TopologicalSpace
open scoped Topology
namespace FTDAP
variable {X Y : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  [TopologicalSpace Y] [DiscreteTopology Y]

/-- A discrete-valued càdlàg path is continuous on a punctured neighborhood
of every time, including endpoints. -/
theorem discrete_cadlag_locally_no_jumps (f : X → Y) (hf : IsCadlag f) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, ContinuousAt f y := by
  obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT x
  have hleft : ∀ᶠ y in 𝓝[<] x, f y = l :=
    hl ((isOpen_discrete ({l} : Set Y)).mem_nhds (mem_singleton l))
  have hright : ∀ᶠ y in 𝓝[>] x, f y = f x :=
    (hf.isRightContinuous x) ((isOpen_discrete ({f x} : Set Y)).mem_nhds (mem_singleton (f x)))
  have hb : ∀ᶠ y in 𝓝 x, (y < x → f y = l) ∧ (x < y → f y = f x) :=
    (eventually_nhdsWithin_iff.mp hleft).and (eventually_nhdsWithin_iff.mp hright)
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hb
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [hUopen.eventually_mem hxU] with y hy hne
  have hne' : y ≠ x := hne
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have he : f =ᶠ[𝓝 y] fun _ => l := by
      filter_upwards [hUopen.eventually_mem hy, isOpen_Iio.eventually_mem hlt] with z hz hzlt
      exact (hUsub hz).1 hzlt
    exact he.continuousAt
  · have he : f =ᶠ[𝓝 y] fun _ => f x := by
      filter_upwards [hUopen.eventually_mem hy, isOpen_Ioi.eventually_mem hgt] with z hz hzgt
      exact (hUsub hz).2 hzgt
    exact he.continuousAt

/-- Discrete-valued càdlàg paths have finitely many discontinuities on every
compact time set. No deterministic bound on their number is assumed. -/
theorem discrete_cadlag_finite_jumps (f : X → Y) (hf : IsCadlag f)
    (K : Set X) (hK : IsCompact K) : {x ∈ K | ¬ ContinuousAt f x}.Finite := by
  have hgood : {x | ContinuousAt f x} ∈ codiscreteWithin K := by
    apply eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
    intro x _
    exact (discrete_cadlag_locally_no_jumps f hf x).mono (fun _ h _ => h)
  exact hK.finite_sdiff_of_mem_codiscreteWithin hgood

#print axioms discrete_cadlag_locally_no_jumps
#print axioms discrete_cadlag_finite_jumps
end FTDAP

namespace FTDAP
open Bornology
variable {X Y : Type*} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
  [MetricSpace Y]

omit [OrderTopology X] in
theorem cadlag_subtype_closed (f : X → Y) (hf : IsCadlag f)
    (E : Set Y) (hE : IsClosed E) (hrange : ∀ x, f x ∈ E) :
    IsCadlag (fun x => (⟨f x, hrange x⟩ : E)) := by
  constructor
  · intro x
    exact tendsto_subtype_rng.mpr (hf.isRightContinuous x)
  · intro x
    by_cases hbot : 𝓝[<] x = ⊥
    · exact ⟨⟨f x, hrange x⟩, by simp [hbot]⟩
    · let : NeBot (𝓝[<] x) := ⟨hbot⟩
      obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT x
      have hlE : l ∈ E := hE.mem_of_tendsto hl (Eventually.of_forall hrange)
      exact ⟨⟨l, hlE⟩, tendsto_subtype_rng.mpr hl⟩

/-- This is the pathwise finite-jump assertion for a compact horizon and a
state set whose intersection with every bounded set is finite. -/
theorem locally_finite_state_cadlag_finite_jumps [CompactSpace X]
    (f : X → Y) (hf : IsCadlag f) (E : Set Y) (hrange : ∀ x, f x ∈ E)
    (hfinite : ∀ B : Set Y, IsBounded B → (E ∩ B).Finite) :
    {x | ¬ ContinuousAt f x}.Finite := by
  let F : Set Y := E ∩ (f '' univ)
  have hF : F.Finite := hfinite _ (isBounded_image_of_isCadlag_of_isCompact hf isCompact_univ)
  have hr : ∀ x, f x ∈ F := fun x => ⟨hrange x, ⟨x, mem_univ x, rfl⟩⟩
  let : DiscreteTopology F := isDiscrete_iff_discreteTopology.mp hF.isDiscrete
  let g : X → F := fun x => ⟨f x, hr x⟩
  have hg : IsCadlag g := cadlag_subtype_closed f hf F hF.isClosed hr
  have hfg : ∀ x, ContinuousAt g x → ContinuousAt f x := by
    intro x hx
    exact continuous_subtype_val.continuousAt.comp hx
  have hh := discrete_cadlag_finite_jumps g hg univ isCompact_univ
  apply hh.subset
  intro x hx
  exact ⟨mem_univ x, fun h => hx (hfg x h)⟩

#print axioms cadlag_subtype_closed
#print axioms locally_finite_state_cadlag_finite_jumps
end FTDAP
