import RefinedMartingaleStops

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The local-martingale converse for the actual finite-jump trading model.
Price boundedness and finite paths produce the variation localization used in
Fatou's lemma; no integrability of the original holdings is required. -/
theorem PriceJumpModel.local_martingale_implies_na
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t)) (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (T : NNReal) (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (E : Set V) (hE : ∀ B : Set V, Bornology.IsBounded B → (E ∩ B).Finite)
    (hstates : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), S t ω ∈ E)
    (κ : ℕ → Ω → NNReal)
    (hκ : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (κ n ω : WithTop NNReal)))
    (hκterm : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, κ n ω = T)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (κ n ω) : NNReal) : ℝ) ω‖ ≤ b n)
    (hlm : HorizonLocalMartingale P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T) :
    GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T := by
  obtain ⟨σ, hσ, _hmon, hσterm, hmart⟩ := hlm
  let ρ := fun n ω => min (κ n ω) (M.tailJumpStop n ω)
  have hρ : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (ρ n ω : WithTop NNReal)) := by
    intro n
    simpa only [ρ, WithTop.coe_min] using (hκ n).min (M.tailJumpStop_stopping n)
  let η := fun n ω => min (σ n ω) (ρ n ω)
  have hη : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (η n ω : WithTop NNReal)) := by
    intro n
    simpa only [η, WithTop.coe_min] using (hσ n).min (hρ n)
  have hρb : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (ρ n ω) : NNReal) : ℝ) ω‖ ≤ b n := by
    intro n
    filter_upwards [hbound n] with ω hω
    intro t ht
    have h := hω (min t (M.tailJumpStop n ω)) ((min_le_left _ _).trans ht)
    simpa only [ρ, min_assoc, min_comm, min_left_comm] using h
  have hηmart : ∀ n, Martingale
      (fun (t : Iic T) ω => S ((min t.val (η n ω) : NNReal) : ℝ) ω)
      (horizonFiltration (nonnegativeFiltration 𝓕) T) P := by
    intro n
    exact bounded_refinement_of_horizon_martingale 𝓕 S hadapt hcad T
      (σ n) (ρ n) (hσ n) (hρ n) (hmart n) (b n) (hρb n)
  have hηterm : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, η n ω = T := by
    filter_upwards [hσterm, hκterm] with ω hσω hκω
    have hs : ∀ᶠ n in atTop, σ n ω = T := eventually_atTop.mpr hσω
    have hk : ∀ᶠ n in atTop, κ n ω = T := eventually_atTop.mpr hκω
    filter_upwards [hs, hk, M.tailJumpStop_eventually_horizon ω] with n hsn hkn htn
    simp only [η, ρ, hsn, hkn, htn, min_self]
  have hvar : ∀ n, ∀ᵐ ω ∂P,
      (∑ k ∈ (M.stop (η n) (hη n)).active ω, ‖M.marks k ω‖) ≤
        (n + 1 : ℕ) * (2 * b n) := by
    intro n
    exact M.localized_jump_variation_bound S T E hE
      (hstates.mono (fun ω hω => ⟨hcad ω, hω⟩)) (κ n) (η n) n (b n) (hb n)
      (fun ω => (min_le_right _ _).trans (min_le_left _ _))
      (fun ω => (min_le_right _ _).trans (min_le_right _ _)) (hbound n)
  exact M.no_arbitrage_of_localized_variation η hη hηterm hηmart
    (fun n => (n + 1 : ℕ) * (2 * b n)) hvar

#print axioms PriceJumpModel.local_martingale_implies_na
end FTDAP
