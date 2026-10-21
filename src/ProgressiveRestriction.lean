import SeparatedRectangles

open MeasureTheory Set
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- Progressive measurability transports from real to nonnegative time. -/
theorem progressive_nonnegative_restriction
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hS : IsStronglyProgressive 𝓕 S) :
    IsStronglyProgressive (nonnegativeFiltration 𝓕) (fun t ω => S (t : ℝ) ω) := by
  intro t
  have hp := hS (t : ℝ)
  let : MeasurableSpace Ω := 𝓕 (t : ℝ)
  let f : Iic t → Iic (t : ℝ) := fun s => ⟨(s.val : ℝ), s.property⟩
  have hf : Measurable f :=
    (NNReal.continuous_coe.comp continuous_subtype_val).measurable.subtype_mk
  exact hp.comp_measurable (hf.prodMap measurable_id)

/-- Adapted real-time cadlag prices therefore give adapted stopped prices on
nonnegative time, with no separate stopped-price measurability premise. -/
theorem stopped_price_strongly_adapted
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω))
    (σ : Ω → NNReal)
    (hσ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (σ ω : WithTop NNReal))) :
    StronglyAdapted (nonnegativeFiltration 𝓕)
      (fun t ω => S ((min t (σ ω) : NNReal) : ℝ) ω) := by
  have hp := progressive_nonnegative_restriction 𝓕 S
    (adapted_right_continuous_progressive 𝓕 S hadapt (fun ω => (hcad ω).isRightContinuous))
  have hs := hp.stronglyAdapted_stoppedProcess hσ
  intro t
  have ht := hs t
  have he : stoppedProcess (fun (t : NNReal) ω => S (t : ℝ) ω) (fun ω => (σ ω : WithTop NNReal)) t =
      (fun ω => S ((min t (σ ω) : NNReal) : ℝ) ω) := by
    funext ω
    simp only [stoppedProcess, ← WithTop.coe_min]
    rfl
  rw [he] at ht
  exact ht

#print axioms progressive_nonnegative_restriction
#print axioms stopped_price_strongly_adapted
end FTDAP
