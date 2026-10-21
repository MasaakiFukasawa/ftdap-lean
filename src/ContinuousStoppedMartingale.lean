import HorizonMartingaleExtension

open MeasureTheory Set Filter
namespace FTDAP
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Bounded stopping preserves a right-continuous real martingale on the
finite horizon. Stopped adaptedness is obtained from progressive measurability
when applying this theorem to the source prices. -/
theorem continuous_stopped_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›} {S : NNReal → Ω → ℝ}
    (hm : Martingale S 𝓕 P) (hr : ∀ ω, IsRightContinuous (fun t => S t ω))
    (σ : Ω → NNReal) (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (ha : StronglyAdapted 𝓕 (fun t ω => S (min t (σ ω)) ω)) (T : NNReal) :
    Martingale (fun (t : Iic T) ω => S (min t.val (σ ω)) ω) (horizonFiltration 𝓕 T) P := by
  have hmin : ∀ t : NNReal,
      IsStoppingTime 𝓕 (fun ω => (min t (σ ω) : WithTop NNReal)) := by
    intro t
    simpa only [WithTop.coe_min] using (isStoppingTime_const 𝓕 t).min hσ
  have hint : ∀ t : NNReal, Integrable (fun ω => S (min t (σ ω)) ω) P := by
    intro t
    exact (martingale_bounded_optional_sampling hm hr _ (hmin t) t
      (fun ω => min_le_left _ _)).1
  apply martingale_of_rectangle_tests P (horizonFiltration 𝓕 T) _ (fun t => ha t.val)
    (fun t => hint t.val)
  intro s t hst A hA
  let B := {ω | s.val < σ ω}
  have hB : MeasurableSet[𝓕 s.val] B := by
    simpa only [WithTop.coe_le_coe, compl_ofPred, not_le] using (hσ s.val).compl
  have hBg : MeasurableSet B := 𝓕.le s.val B hB
  let ρ := fun ω => max s.val (min t.val (σ ω))
  have hρ : IsStoppingTime 𝓕 (fun ω => (ρ ω : WithTop NNReal)) := by
    simpa only [ρ, WithTop.coe_max, WithTop.coe_min] using (isStoppingTime_const 𝓕 s.val).max (hmin t.val)
  obtain ⟨hiρ, heρ⟩ := martingale_bounded_optional_sampling hm hr ρ hρ t.val
    (fun ω => max_le hst (min_le_left _ _))
  have hAB : MeasurableSet[𝓕 s.val] (A ∩ B) := hA.inter hB
  have hABρ : MeasurableSet[hρ.measurableSpace] (A ∩ B) :=
    hρ.le_measurableSpace_of_const_le (fun ω => by
      exact WithTop.coe_le_coe.mpr (le_max_left _ _)) _ hAB
  have he : (fun ω => S (min t.val (σ ω)) ω - S (min s.val (σ ω)) ω) =
      B.indicator (fun ω => S (ρ ω) ω - S s.val ω) := by
    funext ω
    by_cases hb : s.val < σ ω
    · have hρeq : ρ ω = min t.val (σ ω) := max_eq_right (le_min hst hb.le)
      simp only [B, mem_ofPred_eq, hb, indicator_of_mem, min_eq_left hb.le, hρeq]
    · have hσs : σ ω ≤ s.val := le_of_not_gt hb
      have hσt := hσs.trans hst
      simp only [B, mem_ofPred_eq, hb, not_false_eq_true, indicator_of_notMem,
        min_eq_right hσs, min_eq_right hσt, sub_self]
  rw [he, setIntegral_indicator hBg,
    integral_sub hiρ.integrableOn (hm.integrable s.val).integrableOn,
    heρ (A ∩ B) hABρ, ← hm.setIntegral_eq hst hAB, sub_self]

#print axioms continuous_stopped_martingale
end FTDAP
