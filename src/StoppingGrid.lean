import LocalizedVariationNA
import PinnedOptionalSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory Set Filter
open scoped Topology
namespace FTDAP

/-- Round upwards on a mesh of size `1/(n+1)`. -/
noncomputable def ceilGrid (n : ℕ) (x : NNReal) : NNReal :=
  (⌈x * (n + 1 : ℕ)⌉₊ : NNReal) / (n + 1 : ℕ)

theorem ceilGrid_le_iff (n : ℕ) (x t : NNReal) :
    ceilGrid n x ≤ t ↔ x ≤ (⌊t * (n + 1 : ℕ)⌋₊ : NNReal) / (n + 1 : ℕ) := by
  have hd : (0 : NNReal) < (n + 1 : ℕ) := by positivity
  rw [ceilGrid, div_le_iff₀ hd, ← Nat.le_floor_iff (by positivity), Nat.ceil_le,
    le_div_iff₀ hd]

theorem le_ceilGrid (n : ℕ) (x : NNReal) : x ≤ ceilGrid n x := by
  apply (le_div_iff₀ (show (0 : NNReal) < (n + 1 : ℕ) by positivity)).mpr
  exact Nat.le_ceil _

theorem ceilGrid_lt (n : ℕ) (x : NNReal) :
    ceilGrid n x < x + 1 / (n + 1 : ℕ) := by
  have hd : (0 : NNReal) < (n + 1 : ℕ) := by positivity
  rw [ceilGrid, div_lt_iff₀ hd]
  have h := Nat.ceil_lt_add_one (show (0 : NNReal) ≤ x * (n + 1 : ℕ) from bot_le)
  simpa only [add_mul, div_mul_cancel₀ _ (ne_of_gt hd), one_mul] using h

theorem ceilGrid_tendsto (x : NNReal) :
    Tendsto (fun n => ceilGrid n x) atTop (𝓝 x) := by
  apply NNReal.tendsto_coe.mp
  have he : Tendsto (fun n : ℕ => (x : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (x : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (x : ℝ))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he
  · intro n
    exact_mod_cast le_ceilGrid n x
  · intro n
    have h := (ceilGrid_lt n x).le
    exact_mod_cast h

variable {Ω : Type*} [MeasurableSpace Ω]

theorem ceilGrid_stopping {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {σ : Ω → NNReal} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (n : ℕ) : IsStoppingTime 𝓕 (fun ω => (ceilGrid n (σ ω) : WithTop NNReal)) := by
  intro t
  have hd : (0 : NNReal) < (n + 1 : ℕ) := by positivity
  have ht : (⌊t * (n + 1 : ℕ)⌋₊ : NNReal) / (n + 1 : ℕ) ≤ t := by
    rw [div_le_iff₀ hd]
    exact Nat.floor_le (by positivity)
  have hm := hσ ((⌊t * (n + 1 : ℕ)⌋₊ : NNReal) / (n + 1 : ℕ))
  have he : {ω | (ceilGrid n (σ ω) : WithTop NNReal) ≤ t} =
      {ω | (σ ω : WithTop NNReal) ≤ ((⌊t * (n + 1 : ℕ)⌋₊ : NNReal) / (n + 1 : ℕ) : NNReal)} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, ceilGrid_le_iff]
  rw [he]
  exact 𝓕.mono ht _ hm

/-- Capping preserves the stopping-time property and gives countable range. -/
theorem capped_ceilGrid_stopping {𝓕 : Filtration NNReal ‹MeasurableSpace Ω›}
    {σ : Ω → NNReal} (hσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop NNReal)))
    (n : ℕ) (T : NNReal) :
    IsStoppingTime 𝓕 (fun ω => (min (ceilGrid n (σ ω)) T : WithTop NNReal)) := by
  simpa only [WithTop.coe_min] using (ceilGrid_stopping hσ n).min_const T

omit [MeasurableSpace Ω] in
theorem capped_ceilGrid_countable (σ : Ω → NNReal) (n : ℕ) (T : NNReal) :
    (range (fun ω => (min (ceilGrid n (σ ω)) T : WithTop NNReal))).Countable := by
  apply (Set.countable_range (fun k : ℕ =>
    (min ((k : NNReal) / ((n + 1 : ℕ) : NNReal)) T : WithTop NNReal))).mono
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈σ ω * (n + 1 : ℕ)⌉₊, rfl⟩

#print axioms ceilGrid_stopping
#print axioms ceilGrid_tendsto
#print axioms capped_ceilGrid_countable
end FTDAP
