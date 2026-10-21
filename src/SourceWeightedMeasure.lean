import PredictableMeasureUniqueness
import WeightedEnergy

open MeasureTheory Set Filter
open scoped ENNReal
namespace FTDAP
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [MeasurableSpace V]

/-- The terminal product envelope depends only on the price jumps and common c. -/
noncomputable def PriceJumpModel.envelope
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (ω : Ω) : ℝ :=
  ∏ k ∈ M.active ω, (1 + c (M.times k ω, ω) * ‖M.marks k ω‖)

/-- Price variation is bounded by the product minus one, without ordering the
finite set of active indices. -/
theorem finite_variation_product_bound (J : Finset ℕ) (c v : ℕ → ℝ)
    (hc : ∀ k, 1 ≤ c k) (hv : ∀ k, 0 ≤ v k) :
    1 ≤ ∏ k ∈ J, (1 + c k * v k) ∧
      (∑ k ∈ J, v k) ≤ (∏ k ∈ J, (1 + c k * v k)) - 1 := by
  induction J using Finset.induction_on with
  | empty => simp
  | @insert k J hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have hck : 0 ≤ c k := (zero_le_one.trans (hc k))
    have hq : 0 ≤ c k * v k := mul_nonneg hck (hv k)
    have hcv : v k ≤ c k * v k := by nlinarith [mul_nonneg (sub_nonneg.mpr (hc k)) (hv k)]
    have hmul := mul_nonneg hq (sub_nonneg.mpr ih.1)
    constructor <;> nlinarith [ih.1, ih.2]

variable [BorelSpace V]

/-- The price-derived product envelope is measurable despite random finite support. -/
theorem PriceJumpModel.envelope_measurable
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hc : Measurable[𝓕.predictable] c) :
    Measurable (M.envelope c) := by
  have ha : Measurable M.active := measurable_finset_iff.mpr (fun k =>
    measurableSet_setOfPred.mp ((M.stopping k).measurableSpace_le _ (M.measurable_active k)))
  have ht : ∀ k, Measurable (M.times k) := fun k => (M.stopping k).measurable'.untopA
  have hd : ∀ k, Measurable (M.marks k) := fun k =>
    (M.measurable_marks k).mono (M.stopping k).measurableSpace_le le_rfl
  have hcf : ∀ k, Measurable (fun ω => c (M.times k ω, ω)) := fun k =>
    hc.comp (measurable_predictable_atom 𝓕 (M.times k) (ht k))
  have hprod : Measurable (fun p : Finset ℕ × Ω =>
      ∏ k ∈ p.1, (1 + c (M.times k p.2, p.2) * ‖M.marks k p.2‖)) := by
    apply measurable_from_prod_countable_right
    intro J
    exact J.measurable_prod (fun k _ => measurable_const.add ((hcf k).mul (hd k).norm))
  exact hprod.comp (ha.prodMk measurable_id)

/-- The common positive atomic weights used by the compactness proof. -/
noncomputable def PriceJumpModel.energyWeight
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  if k ∈ M.active ω then ENNReal.ofReal
    (‖M.marks k ω‖ / (c (M.times k ω, ω) ^ 2 * M.envelope c ω ^ 3)) else 0

/-- All common atomic weights are measurable. -/
theorem PriceJumpModel.energyWeight_measurable
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hc : Measurable[𝓕.predictable] c) (k : ℕ) :
    Measurable (M.energyWeight c k) := by
  have ht : Measurable (M.times k) := (M.stopping k).measurable'.untopA
  have hd : Measurable (M.marks k) :=
    (M.measurable_marks k).mono (M.stopping k).measurableSpace_le le_rfl
  have hcf := hc.comp (measurable_predictable_atom 𝓕 (M.times k) ht)
  exact (hd.norm.div ((hcf.pow_const 2).mul ((M.envelope_measurable c hc).pow_const 3))).ennreal_ofReal.ite
    ((M.stopping k).measurableSpace_le _ (M.measurable_active k)) measurable_const

omit [BorelSpace V] in
/-- Every actual price jump has strictly positive compactness weight. -/
theorem PriceJumpModel.energyWeight_positive
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hc : ∀ p, 1 ≤ c p) (ω : Ω) (k : ℕ) (hk : k ∈ M.active ω) :
    0 < M.energyWeight c k ω := by
  have hR := (finite_variation_product_bound (M.active ω)
    (fun j => c (M.times j ω, ω)) (fun j => ‖M.marks j ω‖)
    (fun j => hc _) (fun j => norm_nonneg _)).1
  have hRp : 0 < M.envelope c ω := lt_of_lt_of_le zero_lt_one hR
  have hcp : 0 < c (M.times k ω, ω) := lt_of_lt_of_le zero_lt_one (hc _)
  rw [energyWeight, ite_eq_left hk]
  exact ENNReal.ofReal_pos.mpr (div_pos (norm_pos_iff.mpr (M.bounds ω k hk).2.2) (by positivity))

omit [BorelSpace V] in
/-- The common weights have uniformly bounded mass on every path. -/
theorem PriceJumpModel.energyWeight_mass_bound
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hc : ∀ p, 1 ≤ c p) (ω : Ω) :
    (∑' k, M.energyWeight c k ω) ≤ 1 := by
  have hR := finite_variation_product_bound (M.active ω)
    (fun j => c (M.times j ω, ω)) (fun j => ‖M.marks j ω‖)
    (fun j => hc _) (fun j => norm_nonneg _)
  change 1 ≤ M.envelope c ω ∧ (∑ k ∈ M.active ω, ‖M.marks k ω‖) ≤ M.envelope c ω - 1 at hR
  have he := finite_weighted_energy_ennreal (M.active ω) (fun _ => (1 : ℝ))
    (fun j => c (M.times j ω, ω)) (fun j => ‖M.marks j ω‖) (M.envelope c ω) hR.1
    (fun j _ => lt_of_lt_of_le zero_lt_one (hc _)) (fun j _ => norm_nonneg _)
    (fun j _ => by
      rw [norm_one]
      have hp := mul_nonneg (sub_nonneg.mpr (hc (M.times j ω, ω))) (sub_nonneg.mpr hR.1)
      nlinarith [hc (M.times j ω, ω), hR.1]) hR.2
  rw [tsum_eq_sum (f := fun k => M.energyWeight c k ω) (s := M.active ω)
    (fun k hk => by simp only [energyWeight, ite_eq_right hk])]
  have heq : (∑ k ∈ M.active ω, M.energyWeight c k ω) =
      ∑ k ∈ M.active ω, ENNReal.ofReal (‖M.marks k ω‖ /
        (c (M.times k ω, ω) ^ 2 * M.envelope c ω ^ 3)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact ite_eq_left hk
  rw [heq]
  simpa only [norm_one, one_pow, ENNReal.ofReal_one, mul_one] using he

/-- The common finite measure on the actual predictable sigma-algebra. -/
noncomputable def PriceJumpModel.energyMeasure
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) : @Measure (NNReal × Ω) 𝓕.predictable :=
  @jumpMeasure Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable P
    (fun k ω => (M.times k ω, ω)) (M.energyWeight c)

/-- The constructed predictable measure has total mass at most one. -/
theorem PriceJumpModel.energyMeasure_mass
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p) :
    M.energyMeasure c univ ≤ 1 := by
  have ha : ∀ k, @Measurable Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable
      (fun ω => (M.times k ω, ω)) := fun k =>
    measurable_predictable_atom 𝓕 (M.times k) (M.stopping k).measurable'.untopA
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  exact jumpMeasure_mass_le P _ _ ha (M.energyWeight_measurable c hcm) 1
    (Eventually.of_forall (M.energyWeight_mass_bound c hc))

/-- Null sets of the common measure miss every active price jump almost surely. -/
theorem PriceJumpModel.energyMeasure_ae_at_jumps
    {P : Measure Ω} {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (p : NNReal × Ω → Prop) (hp : ∀ᵐ x ∂M.energyMeasure c, p x) :
    ∀ᵐ ω ∂P, ∀ k ∈ M.active ω, p (M.times k ω, ω) := by
  have ha : ∀ k, @Measurable Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable
      (fun ω => (M.times k ω, ω)) := fun k =>
    measurable_predictable_atom 𝓕 (M.times k) (M.stopping k).measurable'.untopA
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  have he := ae_at_jump_atoms P _ _ ha (M.energyWeight_measurable c hcm) p hp
  filter_upwards [he] with ω hω
  intro k hk
  exact hω k (ne_of_gt (M.energyWeight_positive c hc ω k hk))

/-- The source envelope bound puts reduced portfolios in the unit ball of the
actual predictable L2 space. The weighted measure and its density are constructed. -/
theorem PriceJumpModel.energy_memLp [InnerProductSpace ℝ V] [SecondCountableTopology V]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {S : NNReal → Ω → V} {T : NNReal} (M : PriceJumpModel P 𝓕 S T)
    (c : NNReal × Ω → ℝ) (hcm : Measurable[𝓕.predictable] c) (hc : ∀ p, 1 ≤ c p)
    (G : NNReal × Ω → V) (hG : Measurable[𝓕.predictable] G)
    (hbound : ∀ᵐ ω ∂P, ∀ k ∈ M.active ω,
      ‖G (M.times k ω, ω)‖ ≤ c (M.times k ω, ω) * M.envelope c ω) :
    ∃ hL : MemLp G 2 (M.energyMeasure c), ‖hL.toLp G‖ ≤ 1 := by
  have ha : ∀ k, @Measurable Ω (NNReal × Ω) ‹MeasurableSpace Ω› 𝓕.predictable
      (fun ω => (M.times k ω, ω)) := fun k =>
    measurable_predictable_atom 𝓕 (M.times k) (M.stopping k).measurable'.untopA
  let : MeasurableSpace (NNReal × Ω) := 𝓕.predictable
  apply finite_path_portfolio_L2 P _ _ ha (M.energyWeight_measurable c hcm) G hG
    M.active (fun k ω => c (M.times k ω, ω)) (fun k ω => ‖M.marks k ω‖) (M.envelope c)
  filter_upwards [hbound] with ω hω
  have hR := finite_variation_product_bound (M.active ω)
    (fun j => c (M.times j ω, ω)) (fun j => ‖M.marks j ω‖)
    (fun j => hc _) (fun j => norm_nonneg _)
  refine ⟨hR.1, ?_, ?_, hR.2⟩
  · intro k hk
    exact ⟨lt_of_lt_of_le zero_lt_one (hc _), norm_nonneg _, hω k hk, ite_eq_left hk⟩
  · intro k hk
    exact ite_eq_right hk

#print axioms PriceJumpModel.energyMeasure_mass
#print axioms PriceJumpModel.energyMeasure_ae_at_jumps
#print axioms PriceJumpModel.energy_memLp
#print axioms finite_variation_product_bound
#print axioms PriceJumpModel.envelope_measurable
#print axioms PriceJumpModel.energyWeight_measurable
#print axioms PriceJumpModel.energyWeight_positive
#print axioms PriceJumpModel.energyWeight_mass_bound
end FTDAP
