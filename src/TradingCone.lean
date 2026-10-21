import Continuation
import NoFreeLunch

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace FTDAP
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω ι V : Type*} [MeasurableSpace Ω] [LinearOrder ι] [OrderBot ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V]

def AdmissibleStrategy (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (H : ι × Ω → V) : Prop :=
  Measurable[𝓕.predictable] H ∧
    ∃ b : ℝ, 0 < b ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, -b ≤ finiteJumpGain jumps τ Δ H t ω

def tradingCone (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι) :
    Set (WeakClaims P) :=
  {f | ∃ H, AdmissibleStrategy P 𝓕 jumps τ Δ T H ∧
    ∀ᵐ ω ∂P, claimValue P f ω ≤ finiteJumpGain jumps τ Δ H T ω}

theorem finite_gain_zero (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (t : ι) (ω : Ω) :
    finiteJumpGain jumps τ Δ (fun _ => 0) t ω = 0 := by
  simp [finiteJumpGain]

theorem finite_gain_add (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (H G : ι × Ω → V) (t : ι) (ω : Ω) :
    finiteJumpGain jumps τ Δ (H + G) t ω =
      finiteJumpGain jumps τ Δ H t ω + finiteJumpGain jumps τ Δ G t ω := by
  simp only [finiteJumpGain, Pi.add_apply, inner_add_left, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem finite_gain_smul (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (Δ : ℕ → Ω → V) (r : ℝ) (H : ι × Ω → V) (t : ι) (ω : Ω) :
    finiteJumpGain jumps τ Δ (r • H) t ω = r * finiteJumpGain jumps τ Δ H t ω := by
  simp only [finiteJumpGain, Pi.smul_apply, real_inner_smul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem trading_cone_negative_claims (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι) :
    ∀ f : Lp ℝ ∞ P, 0 ≤ f → weakClaim P (-f) ∈ tradingCone P 𝓕 jumps τ Δ T := by
  intro f hf
  refine ⟨fun _ => 0, ⟨measurable_const, 1, zero_lt_one, ?_⟩, ?_⟩
  · exact Eventually.of_forall (fun ω t _ => by rw [finite_gain_zero]; norm_num)
  · filter_upwards [Lp.coeFn_neg f, (Lp.coeFn_nonneg f).mpr hf] with ω hω hn
    change (-f) ω ≤ finiteJumpGain jumps τ Δ (fun _ => 0) T ω
    rw [hω, finite_gain_zero]
    change 0 ≤ f ω at hn
    change -f ω ≤ 0
    linarith

/-- NA for bounded dominated claims is equivalent to NA for possibly unbounded
terminal gains. The nontrivial direction constructs a bounded positive claim. -/
theorem trading_cone_no_arbitrage_iff (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (hterminal_measurable : ∀ H : ι × Ω → V, Measurable[𝓕.predictable] H →
      Measurable (finiteJumpGain jumps τ Δ H T)) :
    (∀ f ∈ tradingCone P 𝓕 jumps τ Δ T, 0 ≤ claimValue P f → f = 0) ↔
      GainNoArbitrage P 𝓕 jumps τ Δ T := by
  constructor
  · intro hna H hH hadm hnonneg
    let X := finiteJumpGain jumps τ Δ H T
    let f : Ω → ℝ := fun ω => min 1 (max 0 (X ω))
    have hfm : Measurable f := measurable_const.min
      (measurable_const.max (hterminal_measurable H hH))
    have hfpos : ∀ ω, 0 ≤ f ω := fun ω => le_min zero_le_one (le_max_left _ _)
    have hfb : ∀ ω, ‖f ω‖ ≤ 1 := by
      intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hfpos ω)]
      exact min_le_left _ _
    have hflp : MemLp f ∞ P := MemLp.of_bound hfm.aestronglyMeasurable 1
      (Eventually.of_forall hfb)
    let F : Lp ℝ ∞ P := hflp.toLp f
    have hFpos : 0 ≤ F := (Lp.coeFn_nonneg F).mp
      ((hflp.coeFn_toLp).mono (fun ω hω => hω ▸ hfpos ω))
    have hFC : weakClaim P F ∈ tradingCone P 𝓕 jumps τ Δ T := by
      refine ⟨H, ⟨hH, hadm⟩, ?_⟩
      filter_upwards [hflp.coeFn_toLp, hnonneg] with ω hω hn
      change F ω ≤ X ω
      rw [hω]
      exact (min_le_right _ _).trans (by rw [max_eq_right hn])
    have heq := hna (weakClaim P F) hFC hFpos
    change F = 0 at heq
    have hzero : f =ᵐ[P] 0 := by
      have he : F =ᵐ[P] (0 : Ω → ℝ) := by rw [heq]; exact Lp.coeFn_zero ℝ ∞ P
      exact hflp.coeFn_toLp.symm.trans he
    filter_upwards [hzero, hnonneg] with ω hω hn
    change 0 ≤ X ω at hn
    have hx : min 1 (X ω) = 0 := by simpa [f, max_eq_right hn] using hω
    change X ω = 0
    rcases min_eq_iff.mp hx with h | h
    · norm_num at h
    · exact h.1
  · intro hna f hf hn
    obtain ⟨H, ⟨hH, hadm⟩, hdom⟩ := hf
    have hgain : ∀ᵐ ω ∂P, 0 ≤ finiteJumpGain jumps τ Δ H T ω := by
      filter_upwards [hdom, (Lp.coeFn_nonneg _).mpr hn] with ω hd hp
      exact hp.trans hd
    have hgzero := hna H hH hadm hgain
    have hfzero : claimValue P f =ᵐ[P] (0 : Ω → ℝ) := by
      filter_upwards [hdom, (Lp.coeFn_nonneg _).mpr hn, hgzero] with ω hd hp hg
      exact le_antisymm (by simpa [hg] using hd) hp
    have he : claimValue P f = (0 : Lp ℝ ∞ P) :=
      Lp.ext (hfzero.trans (Lp.coeFn_zero ℝ ∞ P).symm)
    exact he

theorem trading_cone_add (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (f g : WeakClaims P) (hf : f ∈ tradingCone P 𝓕 jumps τ Δ T)
    (hg : g ∈ tradingCone P 𝓕 jumps τ Δ T) :
    f + g ∈ tradingCone P 𝓕 jumps τ Δ T := by
  obtain ⟨H, ⟨hH, b, hb, hHb⟩, hdomH⟩ := hf
  obtain ⟨G, ⟨hG, c, hc, hGc⟩, hdomG⟩ := hg
  refine ⟨H + G, ⟨hH.add hG, b + c, add_pos hb hc, ?_⟩, ?_⟩
  · filter_upwards [hHb, hGc] with ω hωH hωG t ht
    rw [finite_gain_add]
    linarith [hωH t ht, hωG t ht]
  · filter_upwards [hdomH, hdomG, Lp.coeFn_add (claimValue P f) (claimValue P g)] with ω hdH hdG he
    change (claimValue P f + claimValue P g) ω ≤ finiteJumpGain jumps τ Δ (H + G) T ω
    rw [he, finite_gain_add]
    exact add_le_add hdH hdG

theorem trading_cone_smul (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι)
    (r : ℝ) (hr : 0 ≤ r) (f : WeakClaims P) (hf : f ∈ tradingCone P 𝓕 jumps τ Δ T) :
    r • f ∈ tradingCone P 𝓕 jumps τ Δ T := by
  obtain ⟨H, ⟨hH, b, hb, hHb⟩, hdom⟩ := hf
  refine ⟨r • H, ⟨hH.const_smul r, r * b + 1, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hHb] with ω hω t ht
    rw [finite_gain_smul]
    have h := mul_le_mul_of_nonneg_left (hω t ht) hr
    linarith
  · filter_upwards [hdom, Lp.coeFn_smul r (claimValue P f)] with ω hd he
    change (r • claimValue P f) ω ≤ finiteJumpGain jumps τ Δ (r • H) T ω
    rw [he, finite_gain_smul]
    exact mul_le_mul_of_nonneg_left hd hr

theorem trading_cone_convex (P : Measure Ω) (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι) :
    Convex ℝ (tradingCone P 𝓕 jumps τ Δ T) := by
  intro f hf g hg a b ha hb _
  exact trading_cone_add P 𝓕 jumps τ Δ T _ _
    (trading_cone_smul P 𝓕 jumps τ Δ T a ha f hf)
    (trading_cone_smul P 𝓕 jumps τ Δ T b hb g hg)

/-- NFL for the explicit finite-gain trading cone is equivalent to a normalized
positive separating density. No closedness of the trading cone is assumed here. -/
theorem trading_nfl_iff_density (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (Δ : ℕ → Ω → V) (T : ι) :
    (∀ f ∈ closure (tradingCone P 𝓕 jumps τ Δ T), 0 ≤ claimValue P f → f = 0) ↔
    ∃ Z : Lp ℝ 1 P, (∀ᵐ ω ∂P, 0 < Z ω) ∧
      (∫ ω, Z ω ∂P) = 1 ∧ ∀ f ∈ tradingCone P 𝓕 jumps τ Δ T, claimsPairing P f Z ≤ 0 :=
  no_free_lunch_iff_positive_separator P _
    (trading_cone_convex P 𝓕 jumps τ Δ T)
    (fun r hr f hf => trading_cone_smul P 𝓕 jumps τ Δ T r hr f hf)
    (trading_cone_negative_claims P 𝓕 jumps τ Δ T)

#print axioms trading_cone_no_arbitrage_iff
#print axioms trading_nfl_iff_density
end FTDAP
