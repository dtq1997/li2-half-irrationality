module
public import Li2Unified.Modular.Base.DecayBinomial
public import Li2Unified.Modular.Base.ParameterShift
public import Li2Unified.Modular.Base.ParameterSeries

set_option backward.privateInPublic true

@[expose] public section

/-! the 3-adic denominator of the moment functional.
With G = parameterG (-1/2) (so G(t^k) = moment k), polynomialMoment f = G((t f)').
The binomial moments nu_k = G(binom(t,k)) obey 3 nu_(k+1) = -nu_k - [k=0],
hence v_3(nu_k) >= -(k+1). A route through the shift identity replaces the
manuscript's formal log generating series; the resulting bound is the same. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

/-- G on polynomials, identified with the literal moments. -/
abbrev Gm (P : ℚ[X]) : ℚ := parameterG (-1/2) P

lemma Gm_monomial (k : ℕ) (a : ℚ) : Gm (monomial k a) = a * moment k := by
  rw [Gm, parameterG_monomial, parameterMoment_negHalf]

lemma polynomialMoment_monomial (k : ℕ) (a : ℚ) :
    polynomialMoment (monomial k a) = a * ((k+1 : ℕ) : ℚ) * moment k := by
  unfold polynomialMoment
  rw [Polynomial.sum_monomial_index]
  simp

/-- polynomialMoment f = G((X f)'). -/
theorem polynomialMoment_eq_Gm (f : ℚ[X]) :
    polynomialMoment f = Gm (derivative (X * f)) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [polynomialMoment_add, hf, hg, mul_add, derivative_add, Gm, Gm, Gm, parameterG_add]
  | monomial k a =>
    rw [polynomialMoment_monomial, X_mul_monomial, derivative_monomial, Gm_monomial,
      Nat.add_sub_cancel]

lemma Gm_shift (P : ℚ[X]) : Gm (P.comp (X+1)) = -2 * Gm P - P.eval 1 := by
  have h := parameterG_shift_one (-1/2) (by norm_num) P
  simp only [Gm] at h ⊢
  linarith

def binomMoment (k : ℕ) : ℚ := Gm (binomPoly k)

lemma binomMoment_zero : binomMoment 0 = -1/3 := by
  rw [binomMoment, binomPoly_zero, Gm, ← C_1, ← monomial_zero_left, parameterG_monomial,
    parameterMoment_negHalf, moment_zero]
  ring

lemma binomMoment_succ (k : ℕ) :
    3 * binomMoment (k+1) = -binomMoment k - (binomPoly (k+1)).eval 1 := by
  have h := Gm_shift (binomPoly (k+1))
  rw [binomPoly_succ_comp_add_one, Gm, parameterG_add] at h
  simp only [binomMoment, Gm] at h ⊢
  linarith

/-- G(g) through the Newton coefficients of g at 0. -/
theorem Gm_newton {g : ℚ[X]} {d : ℕ} (hg : g.natDegree ≤ d) :
    Gm g = ∑ k ∈ Finset.range (d+1), newtonCoeff g 0 k * binomMoment k := by
  conv_lhs => rw [newton_expansion hg 0]
  simp only [map_zero, sub_zero, comp_X]
  rw [Gm, parameterG_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [parameterG_C_mul]
  rfl

/-- Derivative values at integers from values at all integers. -/
theorem derivative_eval_VG (p : ℕ) [Fact p.Prime] {f : ℚ[X]} {e : ℕ} (hf : f.natDegree ≤ e)
    (r : ℚ) (hv : ∀ m : ℤ, VG p (f.eval (m:ℚ)) r) (m : ℤ) :
    VG p ((derivative f).eval (m:ℚ)) (r - (Nat.log p e : ℚ)) := by
  rw [derivative_eval_newton hf]
  apply VG.sum
  intro k hk
  have hk' : k + 1 ≤ e := by simp at hk; omega
  have hc : VG p (newtonCoeff f (m:ℚ) (k+1)) r :=
    newtonCoeff_VG p _ r _ fun i _ => by
      have := hv (m + i)
      push_cast at this
      exact this
  have hinv : VG p ((-1:ℚ)^k / ((k:ℚ)+1)) (-(Nat.log p e : ℚ)) := by
    rw [div_eq_mul_inv]
    have h1 : VG p ((-1:ℚ)^k) 0 := by
      have : ((-1:ℚ)^k) = (((-1:ℤ)^k : ℤ) : ℚ) := by push_cast; ring
      rw [this]; exact VG.intCast _
    have h2 := VG.inv_nat (p := p) (j := k+1) (n := e) (by omega) hk'
    push_cast at h2
    simpa using h1.mul h2
  simpa [sub_eq_add_neg] using hc.mul hinv

end
end Li2

end
