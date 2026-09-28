module
public import Mathlib.RingTheory.PowerSeries.Restricted

@[expose] public section

namespace Li2

/-- Scalar multiplication preserves restricted power series. -/
lemma restrictedSeries_smul {R : Type*} [NormedRing R] [IsUltrametricDist R]
    (c : ℝ) {f : PowerSeries R} (hf : PowerSeries.IsRestricted c f) (a : R) :
    PowerSeries.IsRestricted c (a • f) := by
  rw [PowerSeries.smul_eq_C_mul]
  exact PowerSeries.isRestricted.mul c (PowerSeries.isRestricted_C c a) hf

end Li2
end
