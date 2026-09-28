module
public import Li2Unified.Modular.Base.DecayNormalization
public import Li2Unified.Modular.Base.Valuation
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Roots

set_option backward.privateInPublic true

@[expose] public section

/-! binomial polynomials, their integer values, the Newton
(Gregory) expansion of an arbitrary rational polynomial at an arbitrary centre,
and the derivative of binom(x,k) at x=0. -/
open Polynomial fwdDiff
open scoped BigOperators
namespace Li2
noncomputable section

/-- Two rational polynomials agreeing on c+m for every natural m are equal. -/
lemma eq_of_eval_shift_nat {p q : ℚ[X]} (c : ℚ)
    (h : ∀ m : ℕ, p.eval (c + m) = q.eval (c + m)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun m : ℕ => c + (m : ℚ)) := fun a b hab => by
    simpa using hab
  exact (Set.infinite_range_of_injective hinj).mono (by
    rintro _ ⟨m, rfl⟩
    exact h m)

lemma binomPoly_zero : binomPoly 0 = 1 := by simp [binomPoly]

lemma binomPoly_succ_comp_add_one (k : ℕ) :
    (binomPoly (k+1)).comp (X+1) = binomPoly (k+1) + binomPoly k := by
  apply eq_of_eval_shift_nat 0
  intro m
  simp only [zero_add, eval_comp, eval_add, eval_X, eval_one]
  have hm : (m : ℚ) + 1 = ((m+1 : ℕ) : ℚ) := by push_cast; ring
  rw [hm, binomPoly_eval_nat, binomPoly_eval_nat, binomPoly_eval_nat, Nat.choose_succ_succ']
  push_cast
  ring

lemma binomPoly_eval_add_one (k : ℕ) (x : ℚ) :
    (binomPoly (k+1)).eval (x+1) = (binomPoly (k+1)).eval x + (binomPoly k).eval x := by
  have h := congrArg (eval x) (binomPoly_succ_comp_add_one k)
  simpa [eval_comp] using h

/-- binom(m,k) is an integer for every integer m, including negative m. -/
lemma binomPoly_eval_int (k : ℕ) (m : ℤ) : ∃ z : ℤ, (binomPoly k).eval (m : ℚ) = z := by
  induction k generalizing m with
  | zero => exact ⟨1, by simp [binomPoly_zero]⟩
  | succ k ih =>
    have h0 : (binomPoly (k+1)).eval ((0 : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by
      have := binomPoly_eval_nat (k+1) 0
      simpa using this
    induction m using Int.induction_on with
    | zero => exact ⟨0, h0⟩
    | succ i hi =>
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := ih (i : ℤ)
      refine ⟨a + b, ?_⟩
      push_cast
      rw [binomPoly_eval_add_one, ← Int.cast_natCast, ha, hb]
    | pred i hi =>
      obtain ⟨a, ha⟩ := hi
      obtain ⟨b, hb⟩ := ih (-(i : ℤ) - 1)
      refine ⟨a - b, ?_⟩
      have h := binomPoly_eval_add_one k ((-(i:ℤ) - 1 : ℤ) : ℚ)
      have e : ((-(i:ℤ) - 1 : ℤ) : ℚ) + 1 = ((-(i:ℤ) : ℤ) : ℚ) := by push_cast; ring
      rw [e, ha, hb] at h
      push_cast at h ⊢
      linarith

lemma binomPoly_eval_int_VG (p : ℕ) (k : ℕ) (m : ℤ) :
    VG p ((binomPoly k).eval (m : ℚ)) 0 := by
  obtain ⟨z, hz⟩ := binomPoly_eval_int k m
  rw [hz]
  exact VG.intCast z

/-- The k-th forward difference of the values of f, at step 1. -/
def newtonCoeff (f : ℚ[X]) (c : ℚ) (k : ℕ) : ℚ := (Δ_[(1:ℚ)])^[k] (fun x => f.eval x) c

lemma newtonCoeff_eq_sum (f : ℚ[X]) (c : ℚ) (k : ℕ) :
    newtonCoeff f c k = ∑ i ∈ Finset.range (k+1),
      ((-1 : ℚ)^(k-i) * (k.choose i : ℚ)) * f.eval (c + i) := by
  rw [newtonCoeff, fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i _
  simp [zsmul_eq_mul]

lemma newtonCoeff_eq_zero {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) {k : ℕ}
    (hk : d < k) : newtonCoeff f c k = 0 := by
  rw [newtonCoeff]
  have := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := f) (n := k) (by omega)
  exact congrFun this c

/-- **Newton expansion** at an arbitrary rational centre c, degree window d. -/
theorem newton_expansion {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) :
    f = ∑ k ∈ Finset.range (d+1), C (newtonCoeff f c k) * (binomPoly k).comp (X - C c) := by
  apply eq_of_eval_shift_nat c
  intro m
  have hG := shift_eq_sum_fwdDiff_iter (1 : ℚ) (fun x => f.eval x) m c
  simp only [nsmul_eq_mul, mul_one] at hG
  rw [hG, eval_finset_sum]
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, add_sub_cancel_left,
    binomPoly_eval_nat]
  -- extend both ranges to max m d + 1
  have hext : ∀ N, m ≤ N → d ≤ N →
      ∑ k ∈ Finset.range (N+1), (m.choose k : ℚ) * newtonCoeff f c k =
      ∑ k ∈ Finset.range (d+1), newtonCoeff f c k * (m.choose k : ℚ) ∧
      ∑ k ∈ Finset.range (N+1), (m.choose k : ℚ) * newtonCoeff f c k =
      ∑ k ∈ Finset.range (m+1), (m.choose k : ℚ) * newtonCoeff f c k := by
    intro N hm hd
    constructor
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : d+1 ≤ N+1)]
      rw [Finset.sum_eq_zero (s := Finset.Ico (d+1) (N+1)) (fun k hk => by
        rw [newtonCoeff_eq_zero hf c (by simp at hk; omega), mul_zero]), add_zero]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · rw [← Finset.sum_range_add_sum_Ico _ (by omega : m+1 ≤ N+1)]
      rw [Finset.sum_eq_zero (s := Finset.Ico (m+1) (N+1)) (fun k hk => by
        rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega), Nat.cast_zero, zero_mul]), add_zero]
  obtain ⟨h1, h2⟩ := hext (max m d) (le_max_left _ _) (le_max_right _ _)
  change ∑ k ∈ Finset.range (m+1), (m.choose k : ℚ) * newtonCoeff f c k = _
  rw [← h2, h1]

/-- VG bound on Newton coefficients from a window of d+1 consecutive values. -/
lemma newtonCoeff_VG (p : ℕ) [Fact p.Prime] {f : ℚ[X]} (c r : ℚ) (k : ℕ)
    (hv : ∀ i ≤ k, VG p (f.eval (c + i)) r) : VG p (newtonCoeff f c k) r := by
  rw [newtonCoeff_eq_sum]
  apply VG.sum
  intro i hi
  have hcoef : VG p ((-1 : ℚ)^(k-i) * (k.choose i : ℚ)) 0 := by
    have : ((-1 : ℚ)^(k-i) * (k.choose i : ℚ)) = (((-1 : ℤ)^(k-i) * (k.choose i : ℤ) : ℤ) : ℚ) := by
      push_cast; ring
    rw [this]; exact VG.intCast _
  simpa using hcoef.mul (hv i (by simp at hi; omega))

/-- A p-adic bound on d+1 consecutive values at c,...,c+d extends to c+m for every integer m. -/
theorem eval_VG_of_window (p : ℕ) [Fact p.Prime] {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d)
    (c r : ℚ) (hv : ∀ i ≤ d, VG p (f.eval (c + i)) r) (m : ℤ) :
    VG p (f.eval (c + m)) r := by
  have hN := congrArg (eval (c + (m:ℚ))) (newton_expansion hf c)
  rw [hN, eval_finset_sum]
  apply VG.sum
  intro k hk
  have hk' : k ≤ d := by simp at hk; omega
  simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, add_sub_cancel_left]
  simpa using (newtonCoeff_VG p c r k fun i hi => hv i (hi.trans hk')).mul
    (binomPoly_eval_int_VG p k m)

lemma descPochhammer_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ k).eval (-1) = (-1 : ℚ)^k * (k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast
    ring

/-- d/dx binom(x,k+1) at x=0 equals (-1)^k/(k+1). -/
lemma binomPoly_derivative_eval_zero (k : ℕ) :
    (derivative (binomPoly (k+1))).eval 0 = (-1 : ℚ)^k / ((k:ℚ)+1) := by
  rw [binomPoly, derivative_C_mul, eval_mul, eval_C, descPochhammer_succ_left,
    derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero,
    eval_comp, eval_sub, eval_X, eval_one, zero_sub, descPochhammer_eval_neg_one,
    Nat.factorial_succ]
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma binomPoly_derivative_eval_zero_zero : (derivative (binomPoly 0)).eval 0 = 0 := by
  simp [binomPoly_zero]

/-- The derivative at a Newton centre: f'(c)=sum_{k=1}^d Delta^k f(c) (-1)^(k-1)/k. -/
theorem derivative_eval_newton {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) :
    (derivative f).eval c = ∑ k ∈ Finset.range d,
      newtonCoeff f c (k+1) * ((-1 : ℚ)^k / ((k:ℚ)+1)) := by
  conv_lhs => rw [newton_expansion hf c]
  rw [derivative_sum, eval_finset_sum, Finset.sum_range_succ']
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
    derivative_sub, derivative_X, derivative_C, sub_zero, eval_mul, eval_C,
    eval_comp, eval_sub, eval_X, sub_self]
  simp only [eval_one, one_mul, binomPoly_derivative_eval_zero_zero, mul_zero, add_zero]
  exact Finset.sum_congr rfl fun k _ => by rw [binomPoly_derivative_eval_zero]

end
end Li2

end
