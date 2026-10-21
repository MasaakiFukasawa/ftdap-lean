import L1DualRepresentation
import KreinSmulian

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The bounded-claim pairing separates bounded claims. -/
theorem claims_pairing_zero_kernel (P : Measure Ω) [IsFiniteMeasure P]
    (f : Lp ℝ ∞ P) (h : claimsPairingCLM P f = 0) : f = 0 := by
  have hz : claimsPairing P f (densityFromL2 P (claimInL2 P f)) = 0 := by
    change (claimsPairingCLM P f) _ = 0
    rw [h]
    rfl
  rw [pairing_densityFromL2] at hz
  have hzero : claimInL2 P f = 0 := inner_self_eq_zero.mp hz
  have hcoe : claimInL2 P f =ᵐ[P] f := ((Lp.memLp f).mono_exponent (p := 2) le_top).coeFn_toLp
  apply Lp.ext
  filter_upwards [hcoe, Lp.coeFn_zero ℝ 2 P, Lp.coeFn_zero ℝ ∞ P] with ω hf h2 hInf
  rw [hzero] at hf
  rw [h2] at hf
  exact hf.symm.trans hInf.symm

/-- The actual claim-pairing map is injective. -/
theorem claims_pairing_injective (P : Measure Ω) [IsFiniteMeasure P] :
    Function.Injective (claimsPairingCLM P) := by
  intro f g hfg
  have hz : claimsPairingCLM P (f-g) = 0 := by rw [map_sub, hfg, sub_self]
  exact sub_eq_zero.mp (claims_pairing_zero_kernel P _ hz)

/-- The weak claim space is precisely the weak dual of L1, via the constructed
representation theorem; both directions are continuous in their weak topologies. -/
noncomputable def claimWeakDualEquiv (P : Measure Ω) [IsProbabilityMeasure P] :
    WeakClaims P ≃L[ℝ] WeakDual ℝ (Lp ℝ 1 P) := by
  let Φ : WeakClaims P →ₗ[ℝ] WeakDual ℝ (Lp ℝ 1 P) :=
    StrongDual.toWeakDual.toLinearMap.comp (claimsPairingCLM P).toLinearMap
  have hinj : Function.Injective Φ := claims_pairing_injective P
  have hsurj : Function.Surjective Φ := by
    intro L
    obtain ⟨f, _hf, hrep⟩ := l1_dual_representation P (WeakDual.toStrongDual L)
    refine ⟨weakClaim P f, ?_⟩
    apply WeakDual.toStrongDual.injective
    apply ContinuousLinearMap.ext
    intro z
    exact (hrep z).symm
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hcont : Continuous e := WeakDual.continuous_of_continuous_eval (fun z =>
    WeakBilin.eval_continuous (claimsPairing P) z)
  have hcontinv : Continuous e.symm := by
    apply WeakBilin.continuous_of_continuous_eval
    intro z
    have he : (fun L => claimsPairing P (e.symm L) z) =
        (fun L : WeakDual ℝ (Lp ℝ 1 P) => L z) := by
      funext L
      have h := congrArg (fun L : WeakDual ℝ (Lp ℝ 1 P) => L z) (e.apply_symm_apply L)
      exact h
    rw [he]
    exact WeakDual.eval_continuous z
  exact { e with continuous_toFun := hcont, continuous_invFun := hcontinv }

@[simp]
theorem claimWeakDualEquiv_apply (P : Measure Ω) [IsProbabilityMeasure P]
    (f : WeakClaims P) (z : Lp ℝ 1 P) : claimWeakDualEquiv P f z = claimsPairing P f z := rfl

/-- The inverse duality map has the required L-infinity norm bound. -/
theorem claimWeakDualEquiv_inverse_norm (P : Measure Ω) [IsProbabilityMeasure P]
    (L : WeakDual ℝ (Lp ℝ 1 P)) :
    ‖claimValue P ((claimWeakDualEquiv P).symm L)‖ ≤ ‖WeakDual.toStrongDual L‖ := by
  obtain ⟨f, hf, hrep⟩ := l1_dual_representation P (WeakDual.toStrongDual L)
  have he : claimWeakDualEquiv P (weakClaim P f) = L := by
    apply WeakDual.toStrongDual.injective
    apply ContinuousLinearMap.ext
    intro z
    exact (hrep z).symm
  have hinv : (claimWeakDualEquiv P).symm L = weakClaim P f :=
    (claimWeakDualEquiv P).symm_apply_eq.mpr he.symm
  rw [hinv]
  exact hf

/-- The chosen representative of an L-infinity class is bounded by its norm
outside one null set. -/
theorem bounded_claim_ae_norm (P : Measure Ω) (f : Lp ℝ ∞ P) :
    ∀ᵐ ω ∂P, |f ω| ≤ ‖f‖ := by
  have htop : eLpNormEssSup f P ≠ ∞ := by
    simpa only [eLpNorm_exponent_top (Lp.memLp f).aestronglyMeasurable] using (Lp.memLp f).eLpNorm_ne_top
  filter_upwards [enorm_ae_le_eLpNormEssSup f P] with ω hω
  change ‖f ω‖ ≤ ‖f‖
  rw [← toReal_enorm, Lp.norm_def, eLpNorm_exponent_top (Lp.memLp f).aestronglyMeasurable]
  exact ENNReal.toReal_mono htop hω

#print axioms claims_pairing_zero_kernel
#print axioms claims_pairing_injective
#print axioms claimWeakDualEquiv_apply
#print axioms claimWeakDualEquiv_inverse_norm
#print axioms bounded_claim_ae_norm
end FTDAP
