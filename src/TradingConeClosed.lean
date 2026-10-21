import ClaimDuality

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Krein--Smulian applies to the actual weak claim topology via the proved
L-infinity/L1 duality, so bounded-slice closedness gives global closedness. -/
theorem weak_claims_closed_of_bounded_slices (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Set (WeakClaims P)) (hconv : Convex ℝ C)
    (hslice : ∀ r : ℝ, IsClosed {f : WeakClaims P | f ∈ C ∧
      ∀ᵐ ω ∂P, |claimValue P f ω| ≤ r}) : IsClosed C := by
  let e := claimWeakDualEquiv P
  let K := e.symm ⁻¹' C
  have hKconv : Convex ℝ K := hconv.linear_preimage e.symm.toLinearMap
  have hKslices : ∀ r : ℝ, IsClosed (K ∩ {L | ‖WeakDual.toStrongDual L‖ ≤ r}) := by
    intro r
    have he : (K ∩ {L | ‖WeakDual.toStrongDual L‖ ≤ r}) =
        (e.symm ⁻¹' {f : WeakClaims P | f ∈ C ∧ ∀ᵐ ω ∂P, |claimValue P f ω| ≤ r}) ∩
          {L | ‖WeakDual.toStrongDual L‖ ≤ r} := by
      ext L
      constructor
      · intro h
        have hn : ‖claimValue P (e.symm L)‖ ≤ r :=
          (claimWeakDualEquiv_inverse_norm P L).trans h.2
        have hb : ∀ᵐ ω ∂P, |claimValue P (e.symm L) ω| ≤ r :=
          (bounded_claim_ae_norm P _).mono (fun _ hω => hω.trans hn)
        exact ⟨⟨h.1, hb⟩, h.2⟩
      · intro h
        exact ⟨h.1.1, h.2⟩
    rw [he]
    exact ((hslice r).preimage e.symm.continuous).inter (weakdual_norm_ball_closed r)
  have hKclosed := krein_smulian K hKconv hKslices
  have he : C = e ⁻¹' K := by
    ext f
    simp only [K, mem_preimage, e.symm_apply_apply]
  rw [he]
  exact hKclosed.preimage e.continuous

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- NA under the source locally finite price and bounded-localizer assumptions
makes the actual admissible trading cone weak-star closed. All weighted
measure, Hilbert reduction, bounded-slice and Krein--Smulian steps are derived. -/
theorem PriceJumpModel.trading_cone_closed_from_prices
    {P : Measure Ω} [IsProbabilityMeasure P] (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›)
    (S : ℝ → Ω → V) (T : NNReal)
    (M : PriceJumpModel P 𝓕 (fun t => S (t : ℝ)) T)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hpath : ∀ᵐ ω ∂P, IsCadlag (fun t => S t ω) ∧
      ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ m, IsStoppingTime 𝓕 (fun ω => (σ m ω : WithTop NNReal)))
    (hcover : ∀ᵐ ω ∂P, ∃ m, T ≤ σ m ω)
    (b : ℕ → ℝ)
    (hbound : ∀ m, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ m ω) : NNReal) : ℝ) ω‖ ≤ b m)
    (hna : GainNoArbitrage P 𝓕 M.active M.times M.marks T) :
    IsClosed (tradingCone P 𝓕 M.active M.times M.marks T) := by
  obtain ⟨c, hcm, hc, _hmass, hreduce⟩ := M.unit_hilbert_reduction_from_prices 𝓕 S T E hE hpath
    σ hσ hcover b hbound hna
  apply weak_claims_closed_of_bounded_slices P _
    (trading_cone_convex P 𝓕 M.active M.times M.marks T)
  intro r
  exact M.bounded_trading_slice_closed c hcm hc hreduce hna r

#print axioms weak_claims_closed_of_bounded_slices
#print axioms PriceJumpModel.trading_cone_closed_from_prices
end FTDAP
