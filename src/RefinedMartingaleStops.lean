import LocalizedJumpVariation

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

/-- A bounded-price stopping time can refine any of the genuine martingale
stops supplied by a local martingale. -/
theorem bounded_refinement_of_horizon_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t)) (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (T : NNReal) (σ ρ : Ω → NNReal)
    (hσ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (σ ω : WithTop NNReal)))
    (hρ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (ρ ω : WithTop NNReal)))
    (hm : Martingale (fun (t : Iic T) ω => S ((min t.val (σ ω) : NNReal) : ℝ) ω)
      (horizonFiltration (nonnegativeFiltration 𝓕) T) P)
    (b : ℝ) (hbound : ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (ρ ω) : NNReal) : ℝ) ω‖ ≤ b) :
    Martingale (fun (t : Iic T) ω => S ((min t.val (min (σ ω) (ρ ω)) : NNReal) : ℝ) ω)
      (horizonFiltration (nonnegativeFiltration 𝓕) T) P := by
  let X : NNReal → Ω → V := fun t ω => S ((min (min t T) (σ ω) : NNReal) : ℝ) ω
  have hXm : Martingale X (nonnegativeFiltration 𝓕) P :=
    martingale_extend_horizon (S := fun t ω => S ((min t (σ ω) : NNReal) : ℝ) ω) (T := T) hm
  have hXr : ∀ ω, IsRightContinuous (fun t => X t ω) := by
    intro ω
    exact right_continuous_min
      (right_continuous_min (right_continuous_nonnegative (hcad ω).isRightContinuous) (σ ω)) T
  let δ := fun ω => min (ρ ω) (min T (σ ω))
  have hδ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (δ ω : WithTop NNReal)) := by
    simpa only [δ, WithTop.coe_min] using hρ.min ((isStoppingTime_const _ T).min hσ)
  have hXa : StronglyAdapted (nonnegativeFiltration 𝓕) (fun t ω => X (min t (ρ ω)) ω) := by
    have h := stopped_price_strongly_adapted 𝓕 S hadapt hcad δ hδ
    simpa only [X, δ, min_assoc] using h
  have hXb : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X (min t (ρ ω)) ω‖ ≤ b := by
    filter_upwards [hbound] with ω hω
    intro t ht
    have h := hω (min (min t T) (σ ω))
      ((min_le_left _ _).trans (min_le_right t T))
    simpa only [X, min_assoc, min_comm, min_left_comm] using h
  have hstopped := bounded_vector_stopped_martingale hXm hXr ρ hρ hXa T b hXb
  have hη : IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (min (σ ω) (ρ ω) : WithTop NNReal)) := by
    simpa only [WithTop.coe_min] using hσ.min hρ
  have hηa := stopped_price_strongly_adapted 𝓕 S hadapt hcad _ hη
  apply hstopped.congr (fun t => hηa t.val)
  intro t
  apply Eventually.of_forall
  intro ω
  dsimp [X]
  rw [min_eq_left ((min_le_left t.val (ρ ω)).trans t.property)]
  simp only [min_comm, min_left_comm]

#print axioms bounded_refinement_of_horizon_martingale
end FTDAP
