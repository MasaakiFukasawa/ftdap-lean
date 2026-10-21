import L2WeakStarClosed

open MeasureTheory Set
open scoped ENNReal
namespace FTDAP
variable {Ω α ι V : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [LinearOrder ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem lp_claim_slice_convex (P : Measure Ω) (jumps : Ω → Finset ℕ)
    (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α) (Δ : ℕ → Ω → V)
    (weight : ℕ → Ω → ℝ≥0∞) (ha : ∀ n, Measurable (atom n))
    (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (a r : ℝ) (T : ι) :
    Convex ℝ (lpClaimSlice P jumps τ atom Δ weight a r T) := by
  intro f hf g hg u v hu hv huv
  obtain ⟨hfb, H, hHa, hHf⟩ := hf
  obtain ⟨hgb, G, hGa, hGg⟩ := hg
  have hcoe : ∀ᵐ ω ∂P, (u • f + v • g) ω = u * f ω + v * g ω := by
    filter_upwards [Lp.coeFn_add (u • f) (v • g), Lp.coeFn_smul u f,
      Lp.coeFn_smul v g] with ω hadd huf hvg
    rw [hadd, Pi.add_apply, huf, hvg]
    rfl
  have hgain := lp_atom_gain_affine P jumps τ atom Δ weight ha hw hpositive H G u v
  refine ⟨?_, u • H + v • G, ?_, ?_⟩
  · filter_upwards [hfb, hgb, hcoe] with ω hfb hgb he
    rw [he]
    calc
      |u * f ω + v * g ω| ≤ |u * f ω| + |v * g ω| := abs_add_le _ _
      _ = u * |f ω| + v * |g ω| := by rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
      _ ≤ u * r + v * r := add_le_add
        (mul_le_mul_of_nonneg_left hfb hu) (mul_le_mul_of_nonneg_left hgb hv)
      _ = r := by rw [← add_mul, huv, one_mul]
  · filter_upwards [hHa, hGa, hgain] with ω hh hg he t
    rw [he t]
    have hb := add_le_add (mul_le_mul_of_nonneg_left (hh t) hu)
      (mul_le_mul_of_nonneg_left (hg t) hv)
    rw [← add_mul, huv, one_mul] at hb
    exact hb
  · filter_upwards [hHf, hGg, hgain, hcoe] with ω hh hg he hc
    rw [hc, he T]
    exact add_le_add (mul_le_mul_of_nonneg_left hh hu) (mul_le_mul_of_nonneg_left hg hv)

/-- The bounded atom-gain claim slices are closed in the actual weak-star topology. -/
theorem claim_slice_weakstar_closed (P : Measure Ω) [IsFiniteMeasure P]
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι) (atom : ℕ → Ω → α)
    (Δ : ℕ → Ω → V) (weight : ℕ → Ω → ℝ≥0∞)
    (ha : ∀ n, Measurable (atom n)) (hw : ∀ n, Measurable (weight n))
    (hpositive : ∀ᵐ ω ∂P, ∀ k ∈ jumps ω, weight k ω ≠ 0)
    (a r R : ℝ) (T : ι)
    (hreduction : ∀ f ∈ lpClaimSlice P jumps τ atom Δ weight a r T,
      ∃ H : Lp V 2 (jumpMeasure P atom weight), ‖H‖ ≤ R ∧
        (∀ᵐ ω ∂P, ∀ t, -a ≤ atomGain jumps τ atom Δ H t ω) ∧
        ∀ᵐ ω ∂P, f ω ≤ atomGain jumps τ atom Δ H T ω) :
    IsClosed {f : WeakClaims P |
      claimInL2 P (claimValue P f) ∈ lpClaimSlice P jumps τ atom Δ weight a r T} := by
  apply l2_closed_convex_weakstar_closed
  · exact lp_claim_slice_convex P jumps τ atom Δ weight ha hw hpositive a r T
  · exact lp_claim_slice_closed P jumps τ atom Δ weight ha hw hpositive a r R T hreduction

#print axioms lp_claim_slice_convex
#print axioms claim_slice_weakstar_closed
end FTDAP
