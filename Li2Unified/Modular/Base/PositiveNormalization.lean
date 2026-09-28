module
public import Li2Unified.Modular.Base.Normalization

set_option backward.privateInPublic true

@[expose] public section

/-! Choose the positive rational primitive multiplier required in the paper. -/
open Polynomial
namespace Li2
noncomputable section

def primitiveScale (n : ℕ) : ℚ := (primitiveQ_proportional n).choose

lemma primitiveScale_ne_zero (n : ℕ) : primitiveScale n ≠ 0 :=
  (primitiveQ_proportional n).choose_spec.1

lemma primitiveScale_spec (n : ℕ) :
    (primitiveQ n).map (algebraMap ℤ ℚ) = C (primitiveScale n) * Q n :=
  (primitiveQ_proportional n).choose_spec.2

def P (n : ℕ) : ℤ[X] :=
  if 0 < primitiveScale n then primitiveQ n else -primitiveQ n

def d (n : ℕ) : ℚ := |primitiveScale n|

theorem d_pos (n : ℕ) : 0 < d n := abs_pos.mpr (primitiveScale_ne_zero n)

theorem P_eq_d_Q (n : ℕ) : (P n).map (algebraMap ℤ ℚ) = C (d n) * Q n := by
  by_cases h : 0 < primitiveScale n
  · simpa only [P, if_pos h, d, abs_of_pos h] using primitiveScale_spec n
  · have hneg : primitiveScale n < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) (primitiveScale_ne_zero n)
    simp only [P, if_neg h, Polynomial.map_neg, primitiveScale_spec,
      d, abs_of_neg hneg, map_neg, neg_mul]

theorem P_natDegree_le (n : ℕ) : (P n).natDegree ≤ 2*n := by
  unfold P
  split_ifs <;> simpa using primitiveQ_natDegree_le n

theorem P_isPrimitive (n : ℕ) (hn : Q n ≠ 0) : (P n).IsPrimitive := by
  unfold P
  split_ifs
  · exact primitiveQ_isPrimitive n hn
  · apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro r hr
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp (primitiveQ_isPrimitive n hn) r
    simpa using hr

end
end Li2

end
