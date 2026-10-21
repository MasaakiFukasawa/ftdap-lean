import StoppedPortfolioMarks

open MeasureTheory Set
namespace FTDAP
variable {Ω ι : Type*} [MeasurableSpace Ω] [LinearOrder ι]

/-- A stopping-time measurable mark, included at and after its time, is adapted. -/
theorem stopped_mark_adapted (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (τ : Ω → ι) (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι)))
    (Z : Ω → ℝ) (hZ : Measurable[hτ.measurableSpace] Z) (t : ι) :
    Measurable[𝓕 t] (fun ω => if τ ω ≤ t then Z ω else 0) := by
  classical
  intro A hA
  have hmark : MeasurableSet[𝓕 t] ((Z ⁻¹' A) ∩ {ω | τ ω ≤ t}) := by
    simpa using ((hτ.measurableSet (Z ⁻¹' A)).mp (hZ hA)).2 t
  have he : (fun ω => if τ ω ≤ t then Z ω else 0) ⁻¹' A =
      ((Z ⁻¹' A) ∩ {ω | τ ω ≤ t}) ∪
        (if (0 : ℝ) ∈ A then {ω | τ ω ≤ t}ᶜ else ∅) := by
    ext ω
    by_cases ht : τ ω ≤ t <;> by_cases hz : (0 : ℝ) ∈ A <;> simp [ht, hz]
  rw [he]
  apply hmark.union
  split_ifs
  · exact (show MeasurableSet[𝓕 t] {ω | τ ω ≤ t} from by simpa using hτ t).compl
  · exact @MeasurableSet.empty Ω (𝓕 t)

variable {V : Type*} [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [BorelSpace ι] [OrderTopology ι] [SecondCountableTopology ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- Adaptedness of the finite Stieltjes gain follows from stopping-time measurable
price increments and active-jump events. -/
theorem finite_gain_adapted (𝓕 : Filtration ι ‹MeasurableSpace Ω›)
    (jumps : Ω → Finset ℕ) (τ : ℕ → Ω → ι)
    (hτ : ∀ k, IsStoppingTime 𝓕 (fun ω => (τ k ω : WithTop ι)))
    (Δ : ℕ → Ω → V)
    (hΔ : ∀ k, Measurable[(hτ k).measurableSpace] (Δ k))
    (hactive : ∀ k, MeasurableSet[(hτ k).measurableSpace] {ω | k ∈ jumps ω})
    (H : ι × Ω → V) (hH : Measurable[𝓕.predictable] H) (t : ι) :
    Measurable[𝓕 t] (finiteJumpGain jumps τ Δ H t) := by
  classical
  let Z : ℕ → Ω → ℝ := fun k ω =>
    if k ∈ jumps ω then inner ℝ (H (τ k ω, ω)) (Δ k ω) else 0
  have hZ : ∀ k, Measurable[(hτ k).measurableSpace] (Z k) := by
    intro k
    have hhold := predictable_portfolio_stopped_measurable 𝓕 (τ k) (hτ k) H hH
    have hi : Measurable[(hτ k).measurableSpace]
        (fun ω => inner ℝ (H (τ k ω, ω)) (Δ k ω)) :=
      continuous_inner.measurable.comp (hhold.prodMk (hΔ k))
    exact hi.ite (hactive k) measurable_const
  have hterms : ∀ k, Measurable[𝓕 t] (fun ω => if τ k ω ≤ t then Z k ω else 0) :=
    fun k => stopped_mark_adapted 𝓕 (τ k) (hτ k) (Z k) (hZ k) t
  have hm : Measurable[𝓕 t] (fun ω => ∑' k, if τ k ω ≤ t then Z k ω else 0) := by
    let : MeasurableSpace Ω := 𝓕 t
    exact Measurable.tsum hterms
  have he : (fun ω => ∑' k, if τ k ω ≤ t then Z k ω else 0) =
      finiteJumpGain jumps τ Δ H t := by
    funext ω
    rw [tsum_eq_sum (s := jumps ω) (fun k hk => by simp [Z, hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Z, hk]
  rwa [he] at hm

#print axioms stopped_mark_adapted
#print axioms finite_gain_adapted
end FTDAP
