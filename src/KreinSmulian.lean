import KreinSmulianDetectors

open NormedSpace Set Filter
open scoped Topology
namespace FTDAP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norm balls in the dual are weak-star closed. -/
theorem weakdual_norm_ball_closed (r : ℝ) :
    IsClosed {f : WeakDual ℝ E | ‖WeakDual.toStrongDual f‖ ≤ r} := by
  have h := (WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := E) 0 r).isClosed
  have he : (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) r) =
      {f : WeakDual ℝ E | ‖WeakDual.toStrongDual f‖ ≤ r} := by
    ext f
    change dist (WeakDual.toStrongDual f) 0 ≤ r ↔ ‖WeakDual.toStrongDual f‖ ≤ r
    rw [dist_zero_right]
  rwa [he] at h

/-- Closed bounded slices are preserved under continuous preimages whose
images of norm balls are norm bounded. -/
theorem weakdual_slices_preimage (K : Set (WeakDual ℝ E))
    (hslice : ∀ r : ℝ, IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}))
    (F : WeakDual ℝ E → WeakDual ℝ E) (hF : Continuous F)
    (hbound : ∀ r : ℝ, ∃ R : ℝ, ∀ f, ‖WeakDual.toStrongDual f‖ ≤ r →
      ‖WeakDual.toStrongDual (F f)‖ ≤ R) :
    ∀ r : ℝ, IsClosed ((F ⁻¹' K) ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}) := by
  intro r
  obtain ⟨R, hR⟩ := hbound r
  have he : ((F ⁻¹' K) ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r}) =
      (F ⁻¹' (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ R})) ∩
        {f | ‖WeakDual.toStrongDual f‖ ≤ r} := by
    ext f
    exact ⟨fun h => ⟨⟨h.1, hR f h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [he]
  exact ((hslice R).preimage hF).inter (weakdual_norm_ball_closed r)

/-- Krein--Smulian for real Banach preduals: a convex subset of the dual is
weak-star closed if all its intersections with norm balls are weak-star closed.
The compact-slice detector construction and predual separation are proved in
the imported local modules. -/
theorem krein_smulian [CompleteSpace E] (K : Set (WeakDual ℝ E)) (hK : Convex ℝ K)
    (hslice : ∀ r : ℝ, IsClosed (K ∩ {f | ‖WeakDual.toStrongDual f‖ ≤ r})) :
    IsClosed K := by
  apply closure_subset_iff_isClosed.mp
  intro x hxclosure
  by_contra hx
  have hnormclosed := weakdual_slices_norm_closed K hslice
  have hxnorm : WeakDual.toStrongDual x ∈ (StrongDual.toWeakDual ⁻¹' K)ᶜ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hnormclosed.isOpen_compl.mem_nhds hxnorm)
  let α : ℝ := ε / 2
  have hα : 0 < α := by dsimp only [α]; positivity
  let F : WeakDual ℝ E → WeakDual ℝ E := fun f => α • f + x
  let K' := F ⁻¹' K
  have hF : Continuous F := (continuous_id.const_smul α).add continuous_const
  have hK' : Convex ℝ K' := (hK.translate_preimage_left x).smul_preimage α
  have hbounds : ∀ r : ℝ, ∃ R : ℝ, ∀ f : WeakDual ℝ E,
      ‖WeakDual.toStrongDual f‖ ≤ r → ‖WeakDual.toStrongDual (F f)‖ ≤ R := by
    intro r
    refine ⟨α * max r 0 + ‖WeakDual.toStrongDual x‖, ?_⟩
    intro f hf
    change ‖α • WeakDual.toStrongDual f + WeakDual.toStrongDual x‖ ≤ _
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
    have hh := mul_le_mul_of_nonneg_left (hf.trans (le_max_left r 0)) hα.le
    linarith
  have hs' := weakdual_slices_preimage K hslice F hF hbounds
  have havoid : ∀ f ∈ K', 1 < ‖WeakDual.toStrongDual f‖ := by
    intro f hf
    by_contra hn
    have hn' := le_of_not_gt hn
    have hd : dist (WeakDual.toStrongDual (F f)) (WeakDual.toStrongDual x) < ε := by
      rw [@dist_eq_norm (StrongDual ℝ E) ContinuousLinearMap.toSeminormedAddCommGroup]
      change ‖α • WeakDual.toStrongDual f + WeakDual.toStrongDual x - WeakDual.toStrongDual x‖ < ε
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
      have hh := mul_le_mul_of_nonneg_left hn' hα.le
      dsimp only [α] at *
      linarith
    exact (hball hd) hf
  have hzero := zero_not_closure_of_slices_avoiding_unit_ball K' hK' hs' havoid
  let G : WeakDual ℝ E → WeakDual ℝ E := fun f => α⁻¹ • (f - x)
  have hG : Continuous G := (continuous_id.sub continuous_const).const_smul α⁻¹
  have hgmem := mem_closure_image hG.continuousAt hxclosure
  have hsub : G '' K ⊆ K' := by
    rintro _ ⟨f, hf, rfl⟩
    change α • (α⁻¹ • (f - x)) + x ∈ K
    rw [smul_smul, mul_inv_cancel₀ hα.ne', one_smul, sub_add_cancel]
    exact hf
  have hGx : G x = 0 := by simp only [G, sub_self, smul_zero]
  apply hzero
  rw [← hGx]
  exact closure_mono hsub hgmem

#print axioms weakdual_norm_ball_closed
#print axioms weakdual_slices_preimage
#print axioms krein_smulian
end FTDAP
