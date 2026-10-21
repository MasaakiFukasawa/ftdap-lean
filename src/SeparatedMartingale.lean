import ProgressiveRestriction
import MartingaleTests

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The original filtration restricted to the closed trading horizon. -/
def horizonFiltration (𝓕 : Filtration NNReal ‹MeasurableSpace Ω›) (T : NNReal) :
    Filtration (Iic T) ‹MeasurableSpace Ω› where
  seq t := 𝓕 t.val
  mono' := fun _ _ h => 𝓕.mono h
  le' t := 𝓕.le t.val

/-- A normalized positive separator of the actual trading cone makes every
bounded stopped price coordinate a genuine martingale on the horizon. -/
theorem PriceJumpModel.stopped_coordinate_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω)) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (Z : Lp ℝ 1 P) (hZ : ∀ᵐ ω ∂P, 0 < Z ω) (hone : (∫ ω, Z ω ∂P) = 1)
    (hsep : ∀ f ∈ tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T,
      claimsPairing P f Z ≤ 0)
    (v : V) (σ : Ω → NNReal)
    (hσ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (σ ω : WithTop NNReal)))
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ‖S 0 ω‖ ≤ b ∧ ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ ω) : NNReal) : ℝ) ω‖ ≤ b) :
    Martingale
      (fun (t : Iic T) ω => inner ℝ v (S ((min t.val (σ ω) : NNReal) : ℝ) ω))
      (horizonFiltration (nonnegativeFiltration 𝓕) T)
      (P.withDensity (fun ω => ENNReal.ofReal (Z ω))) := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  let : IsProbabilityMeasure Q := (density_equivalent_probability P Z hZ hone).1
  have hs := stopped_price_strongly_adapted 𝓕 S hadapt hcad σ hσ
  have hscalar : ∀ t : NNReal, StronglyMeasurable[(nonnegativeFiltration 𝓕) t]
      (fun ω => inner ℝ v (S ((min t (σ ω) : NNReal) : ℝ) ω)) := by
    intro t
    exact (continuous_const.inner continuous_id).comp_stronglyMeasurable (hs t)
  apply martingale_of_rectangle_tests Q
  · intro t
    exact hscalar t.val
  · intro t
    have hm := (hscalar t.val).mono ((nonnegativeFiltration 𝓕).le t.val)
    have hB : ∀ᵐ ω ∂Q,
        ‖inner ℝ v (S ((min t.val (σ ω) : NNReal) : ℝ) ω)‖ ≤ ‖v‖ * b := by
      filter_upwards [hQP.ae_le hbound] with ω hω
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hω.2 t.val t.property) (norm_nonneg v))
    exact (show MemLp _ 1 Q from MemLp.of_bound hm.aestronglyMeasurable _ hB).integrable le_rfl
  · intro s t hst A hA
    have h := M.rectangle_tests_of_separator Z (hZ.mono (fun _ h => h.le)) hsep v σ hσ b hb
      hbound s.val t.val hst t.property A hA
    simpa only [inner_sub_right] using h

/-- The scalar rectangle tests also identify the full vector-valued stopped
price martingale, using Bochner integration in the complete price space. -/
theorem PriceJumpModel.stopped_price_martingale
    [CompleteSpace V] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ ‹MeasurableSpace Ω›) (S : ℝ → Ω → V)
    (hadapt : ∀ t, Measurable[𝓕 t] (S t))
    (hcad : ∀ ω, IsCadlag (fun t => S t ω)) (T : NNReal)
    (M : PriceJumpModel P (nonnegativeFiltration 𝓕) (fun t => S (t : ℝ)) T)
    (Z : Lp ℝ 1 P) (hZ : ∀ᵐ ω ∂P, 0 < Z ω) (hone : (∫ ω, Z ω ∂P) = 1)
    (hsep : ∀ f ∈ tradingCone P (nonnegativeFiltration 𝓕) M.active M.times M.marks T,
      claimsPairing P f Z ≤ 0)
    (σ : Ω → NNReal)
    (hσ : IsStoppingTime (nonnegativeFiltration 𝓕) (fun ω => (σ ω : WithTop NNReal)))
    (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ ω ∂P, ‖S 0 ω‖ ≤ b ∧ ∀ t : NNReal, t ≤ T →
      ‖S ((min t (σ ω) : NNReal) : ℝ) ω‖ ≤ b) :
    Martingale
      (fun (t : Iic T) ω => S ((min t.val (σ ω) : NNReal) : ℝ) ω)
      (horizonFiltration (nonnegativeFiltration 𝓕) T)
      (P.withDensity (fun ω => ENNReal.ofReal (Z ω))) := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  let : IsProbabilityMeasure Q := (density_equivalent_probability P Z hZ hone).1
  have hs := stopped_price_strongly_adapted 𝓕 S hadapt hcad σ hσ
  let X := fun (t : Iic T) ω => S ((min t.val (σ ω) : NNReal) : ℝ) ω
  have hint : ∀ t : Iic T, Integrable (X t) Q := by
    intro t
    have hm := (hs t.val).mono ((nonnegativeFiltration 𝓕).le t.val)
    have hB : ∀ᵐ ω ∂Q, ‖X t ω‖ ≤ b := by
      filter_upwards [hQP.ae_le hbound] with ω hω
      exact hω.2 t.val t.property
    exact (show MemLp _ 1 Q from MemLp.of_bound hm.aestronglyMeasurable b hB).integrable le_rfl
  apply martingale_of_rectangle_tests Q
  · intro t
    exact hs t.val
  · exact hint
  · intro s t hst A hA
    apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _
      ((hint t).sub (hint s)).integrableOn
    intro v
    exact M.rectangle_tests_of_separator Z (hZ.mono (fun _ h => h.le)) hsep v σ hσ b hb
      hbound s.val t.val hst t.property A hA

#print axioms PriceJumpModel.stopped_price_martingale
#print axioms PriceJumpModel.stopped_coordinate_martingale
end FTDAP
