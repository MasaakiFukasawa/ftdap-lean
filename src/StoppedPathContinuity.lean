import TailJumpLocalizers

open MeasureTheory Set Filter
namespace FTDAP
variable {V : Type*} [TopologicalSpace V]

/-- Right-continuity includes sequences which sometimes equal the base point. -/
theorem right_continuous_Ici {f : NNReal → V} (hf : IsRightContinuous f) (t : NNReal) :
    ContinuousWithinAt f (Ici t) t := by
  have heq : insert t (Ioi t) = Ici t := by
    ext x
    simp only [mem_insert_iff, mem_Ioi, mem_Ici]
    exact ⟨fun h => h.elim (fun h => h.symm.le) LT.lt.le,
      fun h => h.eq_or_lt.elim (fun h => Or.inl h.symm) Or.inr⟩
  rw [← heq]
  exact (hf t).insert

/-- A stopped right-continuous path is right-continuous. -/
theorem right_continuous_min {f : NNReal → V} (hf : IsRightContinuous f) (c : NNReal) :
    IsRightContinuous (fun t => f (min t c)) := by
  intro t
  exact (right_continuous_Ici hf (min t c)).comp
    (f := fun x : NNReal => min x c) (x := t) (s := Ioi t)
    (continuous_id.min continuous_const).continuousWithinAt
    (show MapsTo (fun x : NNReal => min x c) (Ioi t) (Ici (min t c)) from
      fun x hx => (show min t c ≤ min x c from min_le_min hx.le le_rfl))

/-- Restrict a real right-continuous path to nonnegative time. -/
theorem right_continuous_nonnegative {f : ℝ → V} (hf : IsRightContinuous f) :
    IsRightContinuous (fun t : NNReal => f (t : ℝ)) := by
  intro t
  exact (hf (t : ℝ)).comp NNReal.continuous_coe.continuousWithinAt (fun x hx => hx)

#print axioms right_continuous_min
#print axioms right_continuous_nonnegative
end FTDAP
