import SeparatedMartingale

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]

section Definition
variable [NormedSpace ℝ V] [CompleteSpace V]

/-- Local martingales on a finite horizon, witnessed by an increasing sequence
of finite stopping times which is eventually the horizon on almost every path.
Each stopped process is a mathlib martingale. -/
def HorizonLocalMartingale (Q : Measure Ω)
    (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›) (S : NNReal → Ω → V) (T : NNReal) : Prop :=
  ∃ σ : ℕ → Ω → NNReal,
    (∀ n, IsStoppingTime 𝓕 (fun ω => (σ n ω : WithTop NNReal))) ∧
    (∀ ω, Monotone (fun n => σ n ω)) ∧
    (∀ᵐ ω ∂Q, ∃ N, ∀ n ≥ N, σ n ω = T) ∧
    ∀ n, Martingale (fun (t : Iic T) ω => S (min t.val (σ n ω)) ω)
      (horizonFiltration 𝓕 T) Q

end Definition

variable [CompleteSpace V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- A normalized positive cone separator gives an equivalent local martingale
measure for the actual price, with the supplied bounded-price localizers.
Closedness or NA is not assumed to imply the existence of the separator here. -/
theorem PriceJumpModel.equivalent_local_martingale_measure_of_separator
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω)) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (Z : Lp ℝ 1 P) (hZ : ∀ᵐ ω ∂P, 0 < Z ω) (hone : (∫ ω, Z ω ∂P) = 1)
    (hsep : ∀ f ∈ tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T,
      claimsPairing P f Z ≤ 0)
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (σ n ω : WithTop NNReal)))
    (hmon : ∀ ω, Monotone (fun n => σ n ω))
    (hterm : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, σ n ω = T)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ n ω) : NNReal) : ℝ) ω‖ ≤ b n) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
  obtain ⟨hprob, hQP, hPQ⟩ := density_equivalent_probability P Z hZ hone
  refine ⟨Q, hprob, hQP, hPQ, σ, hσ, hmon, hQP.ae_le hterm, ?_⟩
  intro n
  apply M.stopped_price_martingale 𝓕 S hadapt hcad T Z hZ hone hsep (σ n) (hσ n) (b n) (hb n)
  filter_upwards [hbound n] with ω hω
  refine ⟨?_, hω⟩
  simpa only [min_eq_left (show (0 : NNReal) ≤ σ n ω from bot_le), NNReal.coe_zero]
    using hω 0 (bot_le)

/-- NA together with weak-star closedness of the actual trading cone supplies
an equivalent local martingale measure. The closedness premise is discharged from NA and the locally finite state
assumption in TradingConeClosed, and the full implication in ForwardFTAP. -/
theorem PriceJumpModel.equivalent_local_martingale_measure_of_closed_cone
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω)) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (hna : GainNoArbitrage P (nonnegativeFiltration 𝓕) M.active M.times M.marks T)
    (hclosed : IsClosed (tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T))
    (σ : ℕ → Ω → NNReal)
    (hσ : ∀ n, IsStoppingTime (nonnegativeFiltration 𝓕)
      (fun ω => (σ n ω : WithTop NNReal)))
    (hmon : ∀ ω, Monotone (fun n => σ n ω))
    (hterm : ∀ᵐ ω ∂P, ∃ N, ∀ n ≥ N, σ n ω = T)
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ n ω) : NNReal) : ℝ) ω‖ ≤ b n) :
    ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧
      HorizonLocalMartingale Q (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T := by
  have hm : ∀ H : NNReal × Ω → V,
      Measurable[(nonnegativeFiltration 𝓕).predictable] H →
      Measurable (finiteJumpGain M.active M.times M.marks H T) := by
    intro H hH
    exact (M.gain_adapted H hH T).mono ((nonnegativeFiltration 𝓕).le T) le_rfl
  have hcone := (trading_cone_no_arbitrage_iff P (nonnegativeFiltration 𝓕)
    M.active M.times M.marks T hm).mpr hna
  obtain ⟨Z, hZ, hone, hsep⟩ := kreps_yan_normalized_density P _
    (trading_cone_convex P (nonnegativeFiltration 𝓕) M.active M.times M.marks T) hclosed
    (fun r hr f hf => trading_cone_smul P (nonnegativeFiltration 𝓕)
      M.active M.times M.marks T r hr f hf)
    (trading_cone_negative_claims P (nonnegativeFiltration 𝓕) M.active M.times M.marks T)
    hcone
  exact M.equivalent_local_martingale_measure_of_separator 𝓕 S hadapt hcad T Z hZ hone hsep
    σ hσ hmon hterm b hb hbound

#print axioms PriceJumpModel.equivalent_local_martingale_measure_of_closed_cone
#print axioms PriceJumpModel.equivalent_local_martingale_measure_of_separator
end FTDAP
