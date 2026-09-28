module
public import Li2Unified.Modular.Base.DecayQuotient

set_option backward.privateInPublic true

@[expose] public section

/-! the residue denominators of the literal functional.
For 1<=j<=K, prod_{l in [1,K], l != j}(l-j) = (-1)^(j-1)(j-1)!(K-j)!, so
K!/prod = (-1)^(j-1) K binom(K-1,j-1) is an integer. Hence every residue of
C(S_n) D_n^3 b_a b_b at -j is an integer, for all n,a,b and 1<=j<=4n. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def eraseProd (K j : ℕ) : ℚ := ∏ l ∈ (Finset.Icc 1 K).erase j, ((l:ℚ) - (j:ℚ))

lemma D_eval_eq_prod (m : ℕ) (x : ℚ) : (D m).eval x = ∏ l ∈ Finset.Icc 1 m, (x + l) := by
  rw [D, eval_prod]
  simp

lemma eraseProd_base {j : ℕ} (hj : 1 ≤ j) :
    eraseProd j j = (-1:ℚ)^(j-1) * ((j-1).factorial : ℚ) := by
  have hs : (Finset.Icc 1 j).erase j = Finset.Icc 1 (j-1) := by
    ext l; simp; omega
  rw [eraseProd, hs]
  have h := D_eval_eq_prod (j-1) (-(j:ℚ))
  rw [D_eq_desc, eval_comp, eval_add, eval_X, eval_C] at h
  have hc : -(j:ℚ) + ((j-1 : ℕ) : ℚ) = -1 := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hc, descPochhammer_eval_neg_one] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro l _
  ring

lemma eraseProd_succ {K j : ℕ} (hjK : j ≤ K) :
    eraseProd (K+1) j = eraseProd K j * (((K+1 : ℕ) : ℚ) - j) := by
  have hs : (Finset.Icc 1 (K+1)).erase j = insert (K+1) ((Finset.Icc 1 K).erase j) := by
    ext l; simp; omega
  rw [eraseProd, hs, Finset.prod_insert (by simp), eraseProd, mul_comm]

lemma eraseProd_eq {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    eraseProd K j = (-1:ℚ)^(j-1) * ((j-1).factorial : ℚ) * ((K-j).factorial : ℚ) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjK
  induction t with
  | zero => simp [eraseProd_base hj]
  | succ t ih =>
    rw [← add_assoc, eraseProd_succ (by omega), ih (by omega)]
    rw [show j + t + 1 - j = t + 1 by omega, show j + t - j = t by omega, Nat.factorial_succ]
    push_cast
    ring

lemma eraseProd_ne_zero {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) : eraseProd K j ≠ 0 := by
  rw [eraseProd_eq hj hjK]
  have : ((j-1).factorial : ℚ) ≠ 0 := by positivity
  have : ((K-j).factorial : ℚ) ≠ 0 := by positivity
  simp_all

lemma residueScale_eq {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    (K.factorial : ℚ) / eraseProd K j =
      (-1:ℚ)^(j-1) * (K:ℚ) * ((K-1).choose (j-1) : ℚ) := by
  rw [eraseProd_eq hj hjK]
  have hc := Nat.choose_mul_factorial_mul_factorial (n := K-1) (k := j-1) (by omega)
  rw [show K - 1 - (j - 1) = K - j by omega] at hc
  have hK : K.factorial = K * (K-1).factorial := by
    obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le (by omega : 1 ≤ K)
    rw [show 1 + K' - 1 = K' by omega, add_comm, Nat.factorial_succ]
  have hc' : ((K-1).choose (j-1) : ℚ) * ((j-1).factorial : ℚ) * ((K-j).factorial : ℚ) =
      ((K-1).factorial : ℚ) := by exact_mod_cast hc
  have h1 : ((j-1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((K-j).factorial : ℚ) ≠ 0 := by positivity
  rw [hK]
  push_cast
  rw [← hc']
  have hs : ((-1:ℚ)^(j-1))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  field_simp
  linear_combination (-(K:ℚ) * ((K-1).choose (j-1) : ℚ)) * hs

lemma residueScale_VG (p : ℕ) [Fact p.Prime] {K j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) :
    VG p ((K.factorial : ℚ) / eraseProd K j) 0 := by
  rw [residueScale_eq hj hjK]
  have : (-1:ℚ)^(j-1) * (K:ℚ) * ((K-1).choose (j-1) : ℚ) =
      (((-1:ℤ)^(j-1) * K * ((K-1).choose (j-1)) : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact VG.intCast _

/-- The literal residue of the binomial Gram numerator at -j. -/
def gramRes (n a b j : ℕ) : ℚ :=
  (gramNum n a b).eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))

theorem gramRes_VG (p : ℕ) [Fact p.Prime] (n a b : ℕ) {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ 4*n) :
    VG p (gramRes n a b j) 0 := by
  have e : gramRes n a b j = ((4*n).factorial : ℚ) / eraseProd (4*n) j *
      (pab n a b).eval (((-(j:ℤ)) : ℤ) : ℚ) := by
    rw [gramRes, gramNum_eq, eval_mul, eval_C, ← eraseProd]
    push_cast
    ring
  rw [e]
  simpa using (residueScale_VG p hj hjK).mul (pab_eval_int p n a b (-(j:ℤ)))

end
end Li2

end
