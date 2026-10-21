import DiscretePriceFTAP
import NullSetMeasurability

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

omit [NormedSpace ℝ V] [CompleteSpace V] in
/-- Under completeness, every version indistinguishable from a regular price
has measurable stopped sections on the trading horizon. -/
theorem horizon_stopped_adapted_of_regular_version
    {P : Measure Ω} (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcomplete : ∀ N : Set Ω, P N = 0 → ∀ t, MeasurableSet[𝓕 t] N)
    (R S : ℝ → Ω → V) (T : NNReal)
    (hRa : ∀ t, Measurable[𝓕 t] (R t)) (hRc : ∀ ω, IsCadlag (fun t => R t ω))
    (he : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 (T : ℝ), S t ω = R t ω)
    (σ : Ω → NNReal)
    (hσ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (σ ω : WithTop NNReal))) :
    StronglyAdapted (horizonFiltration (nonnegativeFiltration 𝓕) T)
      (fun (t : Iic T) ω => S ((min t.val (σ ω) : NNReal) : ℝ) ω) := by
  intro t
  have hr := stopped_price_strongly_adapted 𝓕 R hRa hRc σ hσ t.val
  apply Measurable.stronglyMeasurable
  apply measurable_of_ae_eq_null_sets (P := P)
    (fun N hN => hcomplete N hN (t.val : ℝ)) hr.measurable
  filter_upwards [he] with ω hω
  exact hω _ ⟨(min t.val (σ ω)).property, (min_le_left _ _).trans t.property⟩

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Local martingales transport between indistinguishable horizon versions,
with stopped adaptedness of the target stated explicitly. -/
theorem horizon_local_martingale_congr
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S R : NNReal → Ω → V} {T : NNReal}
    (hm : HorizonLocalMartingale P 𝓕 S T)
    (he : ∀ᵐ ω ∂P, ∀ t ≤ T, S t ω = R t ω)
    (ha : ∀ σ : Ω → NNReal,
      IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)) →
      StronglyAdapted (horizonFiltration 𝓕 T)
        (fun (t : Iic T) ω => R (min t.val (σ ω)) ω)) :
    HorizonLocalMartingale P 𝓕 R T := by
  obtain ⟨σ, hs, hmon, hterm, hmart⟩ := hm
  refine ⟨σ, hs, hmon, hterm, fun n => (hmart n).congr (ha (σ n) (hs n)) ?_⟩
  intro t
  filter_upwards [he] with ω hω
  exact hω _ ((min_le_left _ _).trans t.property)

#print axioms horizon_stopped_adapted_of_regular_version
#print axioms horizon_local_martingale_congr
end FTDAP
