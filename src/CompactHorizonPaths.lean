import SourceFTAP
import BoundedLocalMartingale

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP
variable {V : Type*} [TopologicalSpace V]

/-- Clamp a real time into the closed trading horizon. -/
def horizonClamp (T : NNReal) (t : ℝ) : Icc (0 : ℝ) (T : ℝ) :=
  ⟨min (max t 0) T, ⟨le_min (le_max_right _ _) T.property, min_le_right _ _⟩⟩

theorem horizonClamp_continuous (T : NNReal) : Continuous (horizonClamp T) :=
  ((continuous_id.max continuous_const).min continuous_const).subtype_mk _

theorem horizonClamp_value (T : NNReal) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    (horizonClamp T t : ℝ) = t := by
  simp only [horizonClamp, max_eq_left ht.1, min_eq_left ht.2]

/-- A cadlag path on the compact subtype has a cadlag constant extension to
real time. Thus the source verification imposes no extra regularity outside
the trading horizon. -/
theorem cadlag_compact_horizon_extension (T : NNReal)
    (f : Icc (0 : ℝ) (T : ℝ) → V) (hf : IsCadlag f) :
    IsCadlag (fun t : ℝ => f (horizonClamp T t)) := by
  have hzero : ∀ t : ℝ, t ≤ 0 → horizonClamp T t = horizonClamp T 0 := by
    intro t ht
    apply Subtype.ext
    simp only [horizonClamp, max_eq_right ht, max_self]
  have htop : ∀ t : ℝ, (T : ℝ) ≤ t → horizonClamp T t = horizonClamp T T := by
    intro t ht
    apply Subtype.ext
    calc
      (horizonClamp T t : ℝ) = (T : ℝ) := by
        change min (max t 0) (T : ℝ) = (T : ℝ)
        rw [max_eq_left (T.property.trans ht), min_eq_right ht]
      _ = (horizonClamp T T : ℝ) := (horizonClamp_value T T ⟨T.property, le_rfl⟩).symm
  refine ⟨?_, ?_⟩
  · intro t
    change Tendsto (fun u => f (horizonClamp T u)) (𝓝[>] t) (𝓝 (f (horizonClamp T t)))
    by_cases ht0 : t < 0
    · have he : (fun u => f (horizonClamp T u)) =ᶠ[𝓝[>] t]
          (fun _ => f (horizonClamp T 0)) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht0)] with u hu
        rw [hzero u hu.le]
      rw [hzero t ht0.le]
      exact tendsto_const_nhds.congr' he.symm
    · by_cases htT : (T : ℝ) ≤ t
      · have he : (fun u => f (horizonClamp T u)) =ᶠ[𝓝[>] t]
            (fun _ => f (horizonClamp T T)) := by
          filter_upwards [self_mem_nhdsWithin] with u hu
          rw [htop u (htT.trans hu.le)]
        rw [htop t htT]
        exact tendsto_const_nhds.congr' he.symm
      · have ht : t ∈ Icc 0 (T : ℝ) := ⟨le_of_not_gt ht0, (lt_of_not_ge htT).le⟩
        apply (hf.isRightContinuous (horizonClamp T t)).tendsto.comp
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(horizonClamp_continuous T).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge htT))] with u hu huT
        change (horizonClamp T t : ℝ) < (horizonClamp T u : ℝ)
        rw [horizonClamp_value T t ht,
          horizonClamp_value T u ⟨ht.1.trans hu.le, huT.le⟩]
        exact hu
  · intro t
    by_cases ht0 : t ≤ 0
    · refine ⟨f (horizonClamp T 0), ?_⟩
      have he : (fun u => f (horizonClamp T u)) =ᶠ[𝓝[<] t]
          (fun _ => f (horizonClamp T 0)) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        rw [hzero u (hu.le.trans ht0)]
      exact tendsto_const_nhds.congr' he.symm
    · by_cases htT : (T : ℝ) < t
      · refine ⟨f (horizonClamp T T), ?_⟩
        have he : (fun u => f (horizonClamp T u)) =ᶠ[𝓝[<] t]
            (fun _ => f (horizonClamp T T)) := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htT)] with u hu
          rw [htop u hu.le]
        exact tendsto_const_nhds.congr' he.symm
      · have ht : t ∈ Icc 0 (T : ℝ) := ⟨(lt_of_not_ge ht0).le, le_of_not_gt htT⟩
        obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (horizonClamp T t)
        refine ⟨l, hl.comp ?_⟩
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(horizonClamp_continuous T).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (lt_of_not_ge ht0))] with u hu hu0
        change (horizonClamp T u : ℝ) < (horizonClamp T t : ℝ)
        rw [horizonClamp_value T t ht,
          horizonClamp_value T u ⟨hu0.le, hu.le.trans ht.2⟩]
        exact hu

#print axioms horizonClamp_continuous
#print axioms horizonClamp_value
#print axioms cadlag_compact_horizon_extension
end FTDAP
