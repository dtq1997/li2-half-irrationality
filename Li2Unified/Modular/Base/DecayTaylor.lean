module
public import Li2Unified.Modular.Base.DecayMu

set_option backward.privateInPublic true

@[expose] public section

/-! Taylor coefficients of order 0,1,2 at an
integer centre. Newton's formula gives
  [x^s] f(c+x) = sum_k Delta^k f(c) [x^s] binom(x,k),
with [x^1] binom(x,k+1) = (-1)^k/(k+1) and [x^2] binom(x,k+1) = (-1)^(k+1) H_k/(k+1).
Hence if all integer values of f have v_p >= r and deg f <= d, the order-s Taylor
coefficient at any integer has v_p >= r - s log_p d, s <= 2. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma binomPoly_succ_eq (k : ℕ) :
    binomPoly (k+1) = C (((k:ℚ)+1)⁻¹) * (binomPoly k * (X - C (k:ℚ))) := by
  rw [binomPoly, binomPoly, descPochhammer_succ_right, Nat.factorial_succ]
  rw [show ((k : ℚ[X])) = C (k:ℚ) by simp]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← C_mul]
  push_cast
  rw [mul_inv]

lemma binomPoly_coeff_zero (k : ℕ) : (binomPoly (k+1)).coeff 0 = 0 := by
  induction k with
  | zero => simp [binomPoly, descPochhammer_one]
  | succ k ih =>
    rw [binomPoly_succ_eq, coeff_C_mul, mul_coeff_zero, ih]
    simp

/-- H_k = sum_{i=1}^k 1/i. -/
def harm (k : ℕ) : ℚ := ∑ i ∈ Finset.Icc 1 k, ((i:ℚ))⁻¹

lemma harm_succ (k : ℕ) : harm (k+1) = harm k + ((k:ℚ)+1)⁻¹ := by
  rw [harm, harm, Finset.sum_Icc_succ_top (by omega)]
  push_cast; ring

lemma binomPoly_coeff_one (k : ℕ) : (binomPoly (k+1)).coeff 1 = (-1:ℚ)^k / ((k:ℚ)+1) := by
  induction k with
  | zero => simp [binomPoly, descPochhammer_one]
  | succ k ih =>
    rw [binomPoly_succ_eq, coeff_C_mul, show (1:ℕ) = 0 + 1 from rfl, coeff_mul_X_sub_C,
      binomPoly_coeff_zero, ih]
    have h1 : ((k:ℚ)+1) ≠ 0 := by positivity
    have h2 : ((k:ℚ)+1+1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma binomPoly_coeff_two (k : ℕ) :
    (binomPoly (k+1)).coeff 2 = (-1:ℚ)^(k+1) * harm k / ((k:ℚ)+1) := by
  induction k with
  | zero => simp [binomPoly, descPochhammer_one, harm, coeff_X]
  | succ k ih =>
    rw [binomPoly_succ_eq, coeff_C_mul, show (2:ℕ) = 1 + 1 from rfl, coeff_mul_X_sub_C,
      binomPoly_coeff_one, ih, harm_succ]
    have h1 : ((k:ℚ)+1) ≠ 0 := by positivity
    have h2 : ((k:ℚ)+1+1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma binomPoly_coeff_VG (p : ℕ) [Fact p.Prime] {k d s : ℕ} (hk : k ≤ d) (hs : s ≤ 2) :
    VG p ((binomPoly k).coeff s) (-(s:ℚ) * (Nat.log p d : ℚ)) := by
  have hL : (0:ℚ) ≤ Nat.log p d := Nat.cast_nonneg _
  have hsign : ∀ j : ℕ, VG p ((-1:ℚ)^j) 0 := fun j => by
    have : ((-1:ℚ)^j) = (((-1:ℤ)^j : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact VG.intCast _
  rcases k with _ | k
  · -- binom(x,0)=1
    rw [binomPoly_zero, coeff_one]
    split_ifs
    · exact (VG.one (p := p)).mono (by nlinarith [(Nat.cast_nonneg s : (0:ℚ) ≤ s)])
    · exact VG.zero _
  interval_cases s
  · rw [binomPoly_coeff_zero]; exact VG.zero _
  · rw [binomPoly_coeff_one, div_eq_mul_inv]
    have h := VG.inv_nat (p := p) (j := k+1) (n := d) (by omega) hk
    push_cast at h
    simpa using (hsign k).mul h
  · rw [binomPoly_coeff_two, div_eq_mul_inv]
    have hinv := VG.inv_nat (p := p) (j := k+1) (n := d) (by omega) hk
    push_cast at hinv
    have hH : VG p (harm k) (-(Nat.log p d : ℚ)) := by
      unfold harm
      apply VG.sum
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
      exact VG.inv_nat (p := p) hi1 (by omega)
    refine (((hsign (k+1)).mul hH).mul hinv).mono ?_
    push_cast
    linarith

/-- Taylor coefficients through Newton coefficients. -/
theorem comp_coeff_newton {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d) (c : ℚ) (s : ℕ) :
    (f.comp (X + C c)).coeff s =
      ∑ k ∈ Finset.range (d+1), newtonCoeff f c k * (binomPoly k).coeff s := by
  conv_lhs => rw [newton_expansion hf c]
  rw [sum_comp, finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comp, C_comp, comp_assoc, sub_comp, X_comp, C_comp, add_sub_cancel_right, comp_X,
    coeff_C_mul]

/-- **Taylor bound.** Integer values with v_p >= r give order-s Taylor coefficients
at every integer with v_p >= r - s log_p d, for s <= 2. -/
theorem taylor_coeff_VG (p : ℕ) [Fact p.Prime] {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d)
    (r : ℚ) (hv : ∀ m : ℤ, VG p (f.eval (m:ℚ)) r) (m : ℤ) {s : ℕ} (hs : s ≤ 2) :
    VG p ((f.comp (X + C (m:ℚ))).coeff s) (r - (s:ℚ) * (Nat.log p d : ℚ)) := by
  rw [comp_coeff_newton hf]
  apply VG.sum
  intro k hk
  have hk' : k ≤ d := by simp at hk; omega
  have hc : VG p (newtonCoeff f (m:ℚ) k) r :=
    newtonCoeff_VG p _ r _ fun i _ => by
      have := hv (m + i)
      push_cast at this
      exact this
  simpa [sub_eq_add_neg, neg_mul] using hc.mul (binomPoly_coeff_VG p hk' hs)

end
end Li2

end
