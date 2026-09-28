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

lemma hasDerivAt_externalFieldH (c : ℝ) (hc : 0 < c) (x : ℝ) :
    HasDerivAt (externalFieldH c) (Real.arctan (x / c)) x := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hq0 : 1 + x ^ 2 / c ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hdiv : HasDerivAt (fun y : ℝ => y / c) (1 / c) x :=
    (hasDerivAt_id x).div_const c
  have hpoly : HasDerivAt (fun y : ℝ => 1 + y ^ 2 / c ^ 2)
      (2 * x / c ^ 2) x := by
    simpa using (((hasDerivAt_id x).fun_pow 2).div_const (c ^ 2)).const_add 1
  have hcancel :
      x * (1 / (1 + (x / c) ^ 2) * (1 / c)) =
        (c / 2) * ((2 * x / c ^ 2) / (1 + x ^ 2 / c ^ 2)) := by
    rw [div_pow]
    field_simp [hc0, hq0] <;> ring
  have h := ((hasDerivAt_id x).mul hdiv.arctan).sub
    ((hpoly.log hq0).const_mul (c / 2))
  change HasDerivAt
    (fun y : ℝ => y * Real.arctan (y / c) -
      (c / 2) * Real.log (1 + y ^ 2 / c ^ 2))
    (Real.arctan (x / c)) x
  refine h.congr_deriv ?_
  simp only [id_eq, one_mul]
  rw [hcancel]
  ring

lemma continuous_externalFieldH (c : ℝ) (hc : 0 < c) :
    Continuous (externalFieldH c) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_externalFieldH c hc x).continuousAt

@[simp] lemma externalFieldH_zero (c : ℝ) : externalFieldH c 0 = 0 := by
  simp [externalFieldH]

lemma externalFieldH_neg (c x : ℝ) : externalFieldH c (-x) = externalFieldH c x := by
  simp only [externalFieldH, neg_div, Real.arctan_neg, neg_mul_neg, neg_sq]

lemma even_externalFieldH (c : ℝ) : Function.Even (externalFieldH c) :=
  externalFieldH_neg c

/-- The literal W from GLOBAL-INTEGRAL-v1, section 2. -/
def originalExternalW (x : ℝ) : ℝ :=
  (3 * externalFieldH 1 x - externalFieldH 4 x) / 2

lemma originalExternalW_eq_formula (x : ℝ) :
    originalExternalW x =
      (3 * (x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2)) -
        (x * Real.arctan (x / 4) - 2 * Real.log (1 + x ^ 2 / 16))) / 2 := by
  norm_num [originalExternalW, externalFieldH]

lemma hasDerivAt_originalExternalW (x : ℝ) :
    HasDerivAt originalExternalW
      ((3 * Real.arctan x - Real.arctan (x / 4)) / 2) x := by
  have h := (((hasDerivAt_externalFieldH 1 (by norm_num) x).const_mul 3).sub
    (hasDerivAt_externalFieldH 4 (by norm_num) x)).div_const 2
  simpa only [originalExternalW, div_one] using h

lemma continuous_originalExternalW : Continuous originalExternalW :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_originalExternalW x).continuousAt

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

lemma continuous_originalExternalV : Continuous originalExternalV :=
  continuous_originalExternalW.const_mul (-2)

end
end Li2

end
