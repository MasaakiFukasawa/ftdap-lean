import JumpCompactness
import TradingGains

open MeasureTheory Set Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace FTDAP
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {Ω α ι V : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [LinearOrder ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

noncomputable def atomGain (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V) (H : α → V) (t : ι) (ω : Ω) : ℝ :=
  ∑ k ∈ jumps ω, if τ k ω ≤ t then ⟪H (atom k ω), Δ k ω⟫ else 0

/-- Convergence at actual atoms gives convergence of every gain value,
simultaneously on a single full-measure set. -/
theorem atom_gain_limits (P : Measure Ω) (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V) (weight : ℕ → Ω → ℝ≥0∞)
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (H : ℕ → α → V) (G : α → V)
    (hlim : ∀ᵐ ω ∂P, ∀ k, weight k ω ≠ 0 →
      Tendsto (fun n => H n (atom k ω)) atTop (𝓝 (G (atom k ω)))) :
    ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => atomGain jumps τ atom Δ (H n) t ω) atTop
      (𝓝 (atomGain jumps τ atom Δ G t ω)) := by
  filter_upwards [hpositive, hlim] with ω hp hl t
  apply tendsto_finsetSum (jumps ω)
  intro k hk
  by_cases hkt : τ k ω ≤ t
  · simp only [ite_eq_left hkt]
    exact (hl k (hp k hk)).inner tendsto_const_nhds
  · simp only [ite_eq_right hkt]
    exact tendsto_const_nhds

/-- Almost-sure gain lower bounds pass to a pathwise atom limit. This includes
both admissibility at all times and domination at the terminal time. -/
theorem atom_gain_lower_bounds_pass (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞)
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (H : ℕ → α → V) (G : α → V) (lower : ι → Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, ∀ k, weight k ω ≠ 0 →
      Tendsto (fun n => H n (atom k ω)) atTop (𝓝 (G (atom k ω))))
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t, lower t ω ≤ atomGain jumps τ atom Δ (H n) t ω) :
    ∀ᵐ ω ∂P, ∀ t, lower t ω ≤ atomGain jumps τ atom Δ G t ω := by
  have hlimits := atom_gain_limits P jumps τ atom Δ weight hpositive H G hlim
  have hall := ae_all_iff.mpr hbound
  filter_upwards [hlimits, hall] with ω hl hb t
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hl t)
    (Eventually.of_forall (fun n => hb n t))

/-- Norm convergence in the weighted L² space preserves all gain lower
constraints; the required almost-sure subsequence and atom transport are derived. -/
theorem lp_atom_gain_constraints_limit (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (H : ℕ → Lp V 2 (jumpMeasure P atom weight)) (G : Lp V 2 (jumpMeasure P atom weight))
    (lower : ι → Ω → ℝ) (hlim : Tendsto H atTop (𝓝 G))
    (hbound : ∀ n, ∀ᵐ ω ∂P, ∀ t, lower t ω ≤ atomGain jumps τ atom Δ (H n) t ω) :
    ∀ᵐ ω ∂P, ∀ t, lower t ω ≤ atomGain jumps τ atom Δ G t ω := by
  obtain ⟨φ, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hatoms := ae_at_jump_atoms P atom weight ha hw
    (fun x => Tendsto (fun n => H (φ n) x) atTop (𝓝 (G x))) hae
  exact atom_gain_lower_bounds_pass P jumps τ atom Δ weight hpositive
    (fun n => H (φ n)) G lower hatoms (fun n => hbound (φ n))

#print axioms atom_gain_limits
#print axioms atom_gain_lower_bounds_pass
#print axioms lp_atom_gain_constraints_limit

theorem lp_atom_gain_constraints_closed (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0) (lower : ι → Ω → ℝ) :
    IsClosed {G : Lp V 2 (jumpMeasure P atom weight) |
      ∀ᵐ ω ∂P, ∀ t, lower t ω ≤ atomGain jumps τ atom Δ G t ω} := by
  apply IsSeqClosed.isClosed
  intro H G hH hlim
  exact lp_atom_gain_constraints_limit P jumps τ atom Δ weight ha hw hpositive H G lower hlim hH

#print axioms lp_atom_gain_constraints_closed

theorem lp_atom_gain_affine (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (G H : Lp V 2 (jumpMeasure P atom weight)) (a b : ℝ) :
    ∀ᵐ ω ∂P, ∀ t, atomGain jumps τ atom Δ
      ((a • G + b • H : Lp V 2 (jumpMeasure P atom weight)) : α → V) t ω =
      a * atomGain jumps τ atom Δ G t ω + b * atomGain jumps τ atom Δ H t ω := by
  have hcoe : ∀ᵐ x ∂jumpMeasure P atom weight,
      (a • G + b • H) x = a • G x + b • H x := by
    filter_upwards [Lp.coeFn_add (a • G) (b • H), Lp.coeFn_smul a G, Lp.coeFn_smul b H]
      with x hadd ha hb
    rw [hadd, Pi.add_apply, ha, hb]
    rfl
  have hatoms := ae_at_jump_atoms P atom weight ha hw _ hcoe
  filter_upwards [hatoms, hpositive] with ω hω hp t
  simp only [atomGain, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkt : τ k ω ≤ t
  · simp only [ite_eq_left hkt, hω k (hp k hk), inner_add_left, real_inner_smul_left]
  · simp [hkt]

theorem lp_atom_gain_constraints_convex (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0) (lower : ι → Ω → ℝ) :
    Convex ℝ {G : Lp V 2 (jumpMeasure P atom weight) |
      ∀ᵐ ω ∂P, ∀ t, lower t ω ≤ atomGain jumps τ atom Δ G t ω} := by
  intro G hG H hH a b ha' hb' hab
  filter_upwards [hG, hH, lp_atom_gain_affine P jumps τ atom Δ weight ha hw hpositive G H a b]
    with ω hg hh he t
  rw [he t]
  have hga := mul_le_mul_of_nonneg_left (hg t) ha'
  have hhb := mul_le_mul_of_nonneg_left (hh t) hb'
  have h := add_le_add hga hhb
  rw [← add_mul, hab, one_mul] at h
  exact h

#print axioms lp_atom_gain_affine
#print axioms lp_atom_gain_constraints_convex
end FTDAP
