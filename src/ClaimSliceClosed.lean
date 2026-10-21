import GainDominationCompactness

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace FTDAP
variable {Ω α ι V : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [LinearOrder ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The bounded dominated claim slice in the explicit atom-gain model. -/
def lpClaimSlice (P : Measure Ω) (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V) (weight : ℕ → Ω → ℝ≥0∞)
    (a r : ℝ) (T : ι) : Set (Lp ℝ 2 P) :=
  {f | (∀ᵐ ω ∂P, |f ω| ≤ r) ∧ ∃ H : Lp V 2 (jumpMeasure P atom weight),
    (∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ H t ω) ∧
    ∀ᵐ ω ∂P, f ω ≤ atomGain jumps τ atom Δ H T ω}

/-- A uniform weighted L² portfolio bound implies closedness of the bounded
claim slice. The projection argument, including terminal domination, is proved. -/
theorem lp_claim_slice_closed (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (a r R : ℝ) (T : ι)
    (hreduction : ∀ f ∈ lpClaimSlice P jumps τ atom Δ weight a r T,
      ∃ H : Lp V 2 (jumpMeasure P atom weight), ‖H‖ ≤ R ∧
        (∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ H t ω) ∧
        ∀ᵐ ω ∂P, f ω ≤ atomGain jumps τ atom Δ H T ω) :
    IsClosed (lpClaimSlice P jumps τ atom Δ weight a r T) := by
  apply IsSeqClosed.isClosed
  intro f F hf hlim
  obtain ⟨φ, _, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  choose H hbounded hadm hdom using (fun n => hreduction (f (φ n)) (hf (φ n)))
  obtain ⟨Y, hYadm, hYdom⟩ := gain_domination_compactness P jumps τ atom Δ weight
    ha hw hpositive H R a T (fun n => f (φ n)) F hbounded hadm hdom hae
  refine ⟨?_, Y, hYadm, hYdom⟩
  have hall : ∀ᵐ ω ∂P, ∀ n, |f (φ n) ω| ≤ r :=
    ae_all_iff.mpr (fun n => (hf (φ n)).1)
  filter_upwards [hall, hae] with ω hω hωlim
  exact le_of_tendsto hωlim.abs (Eventually.of_forall hω)

#print axioms lp_claim_slice_closed
end FTDAP
