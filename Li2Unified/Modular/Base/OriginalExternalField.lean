module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

set_option backward.privateInPublic true

@[expose] public section

namespace Li2
noncomputable section

/-- The generic elementary primitive used by the original external field. -/
def externalFieldH (c x : ℝ) : ℝ :=
  x * Real.arctan (x / c) - (c / 2) * Real.log (1 + x ^ 2 / c ^ 2)

@[simp] lemma externalFieldH_zero (c : ℝ) : externalFieldH c 0 = 0 := by
  simp [externalFieldH]

lemma externalFieldH_neg (c x : ℝ) : externalFieldH c (-x) = externalFieldH c x := by
  simp only [externalFieldH, neg_div, Real.arctan_neg, neg_mul_neg, neg_sq]

/-- The literal W from GLOBAL-INTEGRAL-v1, section 2. -/
def originalExternalW (x : ℝ) : ℝ :=
  (3 * externalFieldH 1 x - externalFieldH 4 x) / 2

lemma originalExternalW_eq_formula (x : ℝ) :
    originalExternalW x =
      (3 * (x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2)) -
        (x * Real.arctan (x / 4) - 2 * Real.log (1 + x ^ 2 / 16))) / 2 := by
  norm_num [originalExternalW, externalFieldH]

@[simp] lemma originalExternalW_zero : originalExternalW 0 = 0 := by
  simp [originalExternalW]

lemma even_originalExternalW : Function.Even originalExternalW := by
  intro x
  simp only [originalExternalW, externalFieldH_neg]

/-- The manuscript convention V = -2 W. -/
def originalExternalV (x : ℝ) : ℝ := -2 * originalExternalW x

@[simp] lemma originalExternalV_zero : originalExternalV 0 = 0 := by
  simp [originalExternalV]

lemma even_originalExternalV : Function.Even originalExternalV := by
  intro x
  simp only [originalExternalV, even_originalExternalW x]

end
end Li2

end
