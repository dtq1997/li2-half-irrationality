module
public import Li2Unified.Modular.Base.DecayResidue
public import Li2Unified.Modular.Base.DecayThreeAdic

set_option backward.privateInPublic true

@[expose] public section

/-! node data. For a prime p and m < p^2, v_p(m!) = m/p.
For n < j <= K the literal residue scale r_j = D_n(-j)^3 / eraseProd K j equals
±((j-1)!)^2/(((j-1-n)!)^3 (K-j)!), so when K < p^2 its exact valuation is
2((j-1)/p) - 3((j-1-n)/p) - (K-j)/p. For j <= n, D_n(-j) = 0. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma padicValRat_factorial_small (p : ℕ) [hp : Fact p.Prime] {m : ℕ} (hm : m < p^2) :
    padicValRat p (m.factorial : ℚ) = ((m / p : ℕ) : ℤ) := by
  rw [padicValRat.of_nat]
  have hlog : Nat.log p m < 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · exact Nat.log_lt_of_lt_pow (by omega) hm
  rw [padicValNat_factorial hlog]
  simp

lemma D_eval_neg_of_lt (n j : ℕ) (hnj : n < j) :
    (D n).eval (-(j:ℚ)) = (-1:ℚ)^n * (((j-1).factorial : ℚ) / ((j-1-n).factorial : ℚ)) := by
  induction n with
  | zero =>
    have : ((j-1).factorial : ℚ) ≠ 0 := by positivity
    simp [D, div_self this]
  | succ n ih =>
    rw [D_succ, eval_mul, ih (by omega), eval_add, eval_X, eval_C]
    have e : j - 1 - n = (j - 1 - (n+1)) + 1 := by omega
    rw [e, Nat.factorial_succ]
    have h1 : ((j - 1 - (n+1)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((j - 1 - (n+1) + 1 : ℕ) : ℚ) = (j:ℚ) - n - 1 := by
      rw [show j - 1 - (n+1) + 1 = j - (n+1) by omega, Nat.cast_sub (by omega)]; push_cast; ring
    push_cast at h2 ⊢
    rw [h2]
    have h3 : (j:ℚ) - n - 1 ≠ 0 := by
      have : ((n:ℚ) + 1) < j := by exact_mod_cast hnj
      linarith
    field_simp
    ring

lemma D_eval_neg_of_le {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : (D n).eval (-(j:ℚ)) = 0 := by
  rw [D_eval_eq_prod]
  exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨h1, h2⟩) (by ring)

/-- The residue scale at the node -j. -/
def rscale (n K j : ℕ) : ℚ := (D n).eval (-(j:ℚ)) ^ 3 / eraseProd K j

lemma padicValRat_neg_one_pow (p : ℕ) [Fact p.Prime] (m : ℕ) : padicValRat p ((-1:ℚ)^m) = 0 := by
  rw [padicValRat.pow (by norm_num), padicValRat.neg]; simp

theorem rscale_val (p : ℕ) [hp : Fact p.Prime] {n K j : ℕ} (hnj : n < j) (hjK : j ≤ K)
    (hK : K < p^2) :
    padicValRat p (rscale n K j) =
      2 * (((j-1)/p : ℕ) : ℤ) - 3 * (((j-1-n)/p : ℕ) : ℤ) - (((K-j)/p : ℕ) : ℤ) := by
  have h1 : ((j-1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((j-1-n).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((K-j).factorial : ℚ) ≠ 0 := by positivity
  have hs1 : (-1:ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs2 : (-1:ℚ)^(j-1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD : (D n).eval (-(j:ℚ)) ≠ 0 := by
    rw [D_eval_neg_of_lt n j hnj]; exact mul_ne_zero hs1 (div_ne_zero h1 h2)
  have hE : eraseProd K j ≠ 0 := eraseProd_ne_zero (by omega) hjK
  rw [rscale, padicValRat.div (pow_ne_zero _ hD) hE, padicValRat.pow hD,
    D_eval_neg_of_lt n j hnj, eraseProd_eq (by omega) hjK,
    padicValRat.mul hs1 (div_ne_zero h1 h2), padicValRat.div h1 h2,
    padicValRat.mul (mul_ne_zero hs2 h1) h3, padicValRat.mul hs2 h1,
    padicValRat_neg_one_pow, padicValRat_neg_one_pow,
    padicValRat_factorial_small p (by omega : j - 1 < p^2),
    padicValRat_factorial_small p (by omega : j - 1 - n < p^2),
    padicValRat_factorial_small p (by omega : K - j < p^2)]
  ring

/-- tau_j has v_p >= -2 when j <= K < p^2 and p != 2. -/
lemma tau_VG_small (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {j K : ℕ} (hjK : j ≤ K) (hK : K < p^2) :
    VG p (tau j) (-2) := by
  have h := tau_VG_of_ne_two p hp2 hjK
  refine h.mono ?_
  have : Nat.log p K ≤ 1 := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · simp [h0]
    · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hK)
  have : ((Nat.log p K : ℕ) : ℚ) ≤ 1 := by exact_mod_cast this
  linarith

lemma negTwo_pow_unit (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (j : ℕ) : VG p ((-2:ℚ)^j) 0 := by
  have : ((-2:ℚ)^j) = (((-2:ℤ)^j : ℤ) : ℚ) := by push_cast; ring
  rw [this]; exact VG.intCast _

end
end Li2

end
