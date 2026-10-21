import LocalMartingaleVersions

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CompleteSpace V]

/-- A bounded finite-horizon local martingale is a true martingale. -/
theorem bounded_horizon_local_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›} {S : NNReal → Ω → V} {T : NNReal}
    (hm : HorizonLocalMartingale P 𝓕 S T)
    (ha : StronglyAdapted (horizonFiltration 𝓕 T) (fun (t : Iic T) => S t.val))
    (b : ℝ) (hbound : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖S t ω‖ ≤ b) :
    Martingale (fun (t : Iic T) => S t.val) (horizonFiltration 𝓕 T) P := by
  obtain ⟨σ, _hs, _hmon, hterm, hmart⟩ := hm
  have hint : ∀ t : Iic T, Integrable (S t.val) P := by
    intro t
    exact (show MemLp _ 1 P from MemLp.of_bound
      ((ha t).mono (𝓕.le t.val)).aestronglyMeasurable b
      (hbound.mono (fun _ hω => hω t.val t.property))).integrable le_rfl
  apply martingale_of_rectangle_tests P (horizonFiltration 𝓕 T) _ ha hint
  intro s t hst A hA
  let Y := fun n ω => S (min t.val (σ n ω)) ω - S (min s.val (σ n ω)) ω
  have hi : ∀ n, Integrable (Y n) (P.restrict A) := fun n =>
    (((hmart n).integrable t).sub ((hmart n).integrable s)).integrableOn
  have hB : ∀ n, ∀ᵐ ω ∂(P.restrict A), ‖Y n ω‖ ≤ 2 * b := by
    intro n
    apply ae_restrict_of_ae
    filter_upwards [hbound] with ω hω
    exact (norm_sub_le _ _).trans (by
      linarith [hω (min t.val (σ n ω)) ((min_le_left _ _).trans t.property),
        hω (min s.val (σ n ω)) ((min_le_left _ _).trans s.property)])
  have hlim : ∀ᵐ ω ∂(P.restrict A), Tendsto (fun n => Y n ω) atTop
      (𝓝 (S t.val ω - S s.val ω)) := by
    apply ae_restrict_of_ae
    filter_upwards [hterm] with ω hω
    have he : (fun n => Y n ω) =ᶠ[atTop] (fun _ => S t.val ω - S s.val ω) := by
      obtain ⟨N, hN⟩ := hω
      apply eventually_atTop.mpr
      refine ⟨N, fun n hn => ?_⟩
      simp only [Y, hN n hn, min_eq_left (Set.mem_Iic.mp t.property), min_eq_left (Set.mem_Iic.mp s.property)]
    exact tendsto_const_nhds.congr' he.symm
  have hconv := tendsto_integral_of_dominated_convergence (fun _ => 2 * b)
    (fun n => (hi n).aestronglyMeasurable) (integrable_const _) hB hlim
  have he : ∀ n, (∫ ω in A, Y n ω ∂P) = 0 := by
    intro n
    dsimp [Y]
    rw [integral_sub ((hmart n).integrable t).integrableOn ((hmart n).integrable s).integrableOn,
      ← (hmart n).setIntegral_eq hst hA, sub_self]
  exact tendsto_nhds_unique (hconv.congr (fun n => he n)) tendsto_const_nhds

#print axioms bounded_horizon_local_martingale
end FTDAP
