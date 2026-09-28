module
public import Li2Unified.Modular.Base.DecayMu
public import Li2Unified.Modular.Base.PoleFamily
public import Mathlib.Data.Nat.Choose.Factorization

set_option backward.privateInPublic true

@[expose] public section

/-! the polynomial part of every binomial Gram entry.
Put K=4n, N=3n+a+b and p_ab = binom(t+n,n)^3 binom(t,a) binom(t,b). Then
C(S_n) D_n^3 b_a b_b = C(K!) p_ab, and expanding p_ab in the Newton basis
binom(t+K,k) gives
  (C(S_n) D_n^3 b_a b_b) /ₘ D_K = sum_{K<=k<=N} c_k/binom(k,K) * binom(t,k-K),
with c_k the integer Newton coefficients. Consequently every integer value of
the quotient has v_p >= -log_p N, for every prime p. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma D_succ (m : ℕ) : D (m+1) = D m * (X + C ((m:ℚ)+1)) := by
  rw [D, Finset.prod_Icc_succ_top (by omega)]
  push_cast
  rfl

lemma D_eq_desc (m : ℕ) : D m = (descPochhammer ℚ m).comp (X + C (m:ℚ)) := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    rw [D_succ, ih, descPochhammer_succ_left, mul_comp, X_comp, comp_assoc]
    have h : (X - 1 : ℚ[X]).comp (X + C ((m+1 : ℕ) : ℚ)) = X + C (m:ℚ) := by
      rw [sub_comp, X_comp, one_comp]
      push_cast
      rw [map_add, map_one]
      ring
    rw [h, mul_comm]
    push_cast
    rfl

lemma D_natDegree (m : ℕ) : (D m).natDegree = m := by
  rw [D_eq_desc, natDegree_comp, descPochhammer_natDegree, natDegree_X_add_C, mul_one]

lemma desc_eq_C_mul_binomPoly (m : ℕ) :
    descPochhammer ℚ m = C (m.factorial : ℚ) * binomPoly m := by
  rw [binomPoly, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (by positivity), C_1, one_mul]

/-- binom(t+n,n). -/
def shiftBinom (n : ℕ) : ℚ[X] := (binomPoly n).comp (X + C (n:ℚ))

lemma D_eq_shiftBinom (n : ℕ) : D n = C (n.factorial : ℚ) * shiftBinom n := by
  rw [D_eq_desc, desc_eq_C_mul_binomPoly, mul_comp, C_comp, shiftBinom]

/-- binom(t+n,n)^3 binom(t,a) binom(t,b). -/
def pab (n a b : ℕ) : ℚ[X] := shiftBinom n ^ 3 * binomPoly a * binomPoly b

/-- The literal binomial Gram numerator. -/
def gramNum (n a b : ℕ) : ℚ[X] := C (Sn n) * (D n)^3 * binomPoly a * binomPoly b

lemma gramNum_eq (n a b : ℕ) :
    gramNum n a b = C ((4*n).factorial : ℚ) * pab n a b := by
  have hs : Sn n * ((n.factorial : ℚ))^3 = ((4*n).factorial : ℚ) := by
    rw [Sn]; field_simp
  rw [gramNum, pab, D_eq_shiftBinom, mul_pow, ← C_pow, ← hs, C_mul]
  ring

lemma shiftBinom_eval_int (p n : ℕ) (m : ℤ) : VG p ((shiftBinom n).eval (m:ℚ)) 0 := by
  rw [shiftBinom, eval_comp, eval_add, eval_X, eval_C]
  have := binomPoly_eval_int_VG p n (m + n)
  push_cast at this
  exact this

lemma pab_eval_int (p : ℕ) [Fact p.Prime] (n a b : ℕ) (m : ℤ) :
    VG p ((pab n a b).eval (m:ℚ)) 0 := by
  rw [pab, eval_mul, eval_mul, eval_pow]
  have h := (((shiftBinom_eval_int p n m).pow 3).mul (binomPoly_eval_int_VG p a m)).mul
    (binomPoly_eval_int_VG p b m)
  simpa using h

lemma shiftBinom_natDegree (n : ℕ) : (shiftBinom n).natDegree = n := by
  rw [shiftBinom, natDegree_comp, binomPoly_natDegree, natDegree_X_add_C, mul_one]

lemma pab_natDegree_le (n a b : ℕ) : (pab n a b).natDegree ≤ 3*n + a + b := by
  unfold pab
  refine (natDegree_mul_le).trans ?_
  refine add_le_add ((natDegree_mul_le).trans (add_le_add ((natDegree_pow_le).trans ?_) ?_)) ?_
  · rw [shiftBinom_natDegree]
  · rw [binomPoly_natDegree]
  · rw [binomPoly_natDegree]

lemma D_eval_nat (K m : ℕ) :
    (D K).eval (m:ℚ) = (K.factorial : ℚ) * ((m+K).choose K : ℚ) := by
  rw [D_eq_desc, eval_comp, eval_add, eval_X, eval_C,
    show (m:ℚ) + K = ((m+K : ℕ) : ℚ) by push_cast; ring,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- K! binom(t+K,k) = D_K binom(t,k-K)/binom(k,K) for K <= k. -/
lemma shifted_binom_ratio {K k : ℕ} (hk : K ≤ k) :
    C (K.factorial : ℚ) * (binomPoly k).comp (X + C (K:ℚ)) =
      D K * (C ((k.choose K : ℚ)⁻¹) * binomPoly (k - K)) := by
  apply eq_of_eval_shift_nat 0
  intro m
  simp only [zero_add, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  rw [D_eval_nat, show (m:ℚ) + K = ((m+K : ℕ) : ℚ) by push_cast; ring,
    binomPoly_eval_nat, binomPoly_eval_nat]
  have hc : (k.choose K : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have key : (m+K).choose k * k.choose K = (m+K).choose K * m.choose (k-K) := by
    have := Nat.choose_mul (n := m+K) (k := k) (s := K) hk
    rwa [Nat.add_sub_cancel] at this
  have key' : ((m+K).choose k : ℚ) * (k.choose K : ℚ) = ((m+K).choose K : ℚ) * (m.choose (k-K) : ℚ) := by
    exact_mod_cast key
  field_simp
  linear_combination key'

/-- Newton coefficients of p_ab at -K. -/
def quotCoeff (n a b k : ℕ) : ℚ := newtonCoeff (pab n a b) (-(((4*n : ℕ)) : ℚ)) k

/-- The literal polynomial part of the binomial Gram entry. -/
theorem gramNum_divByMonic (n a b : ℕ) :
    gramNum n a b /ₘ D (4*n) = ∑ k ∈ Finset.Ico (4*n) (3*n+a+b+1),
      C (quotCoeff n a b k * ((k.choose (4*n) : ℚ))⁻¹) * binomPoly (k - 4*n) := by
  set K := 4*n with hK
  set N := 3*n+a+b with hN
  have hexp := newton_expansion (pab_natDegree_le n a b) (-((K : ℕ) : ℚ))
  have hshift : (X - C (-((K:ℕ):ℚ)) : ℚ[X]) = X + C (K:ℚ) := by
    rw [map_neg, sub_neg_eq_add]
  simp only [hshift] at hexp
  set g : ℕ → ℚ[X] := fun k => C (quotCoeff n a b k) *
    (C (K.factorial : ℚ) * (binomPoly k).comp (X + C (K:ℚ))) with hg
  have hF : gramNum n a b = ∑ k ∈ Finset.range (N+1), g k := by
    rw [gramNum_eq, hexp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hg, quotCoeff]
    ring
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N+1)) (fun k => k < K)] at hF
  have hhigh : (Finset.range (N+1)).filter (fun k => ¬ k < K) = Finset.Ico K (N+1) := by
    ext k; simp; omega
  rw [hhigh] at hF
  set r := ∑ k ∈ (Finset.range (N+1)).filter (fun k => k < K), g k with hr
  refine (div_modByMonic_unique _ r (D_monic K) ⟨?_, ?_⟩).1
  · rw [hF, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : K ≤ k := (Finset.mem_Ico.mp hk).1
    simp only [hg]
    rw [shifted_binom_ratio hk', C_mul]
    ring
  · rw [degree_eq_natDegree (D_monic K).ne_zero, D_natDegree]
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · have : (Finset.range (N+1)).filter (fun k => k < K) = ∅ := by
        ext k; simp; omega
      rw [hr, this, Finset.sum_empty, degree_zero, h0]
      exact WithBot.bot_lt_coe _
    · have hnat : r.natDegree ≤ K - 1 := by
        apply natDegree_sum_le_of_forall_le
        intro k hk
        have hkK : k < K := (Finset.mem_filter.mp hk).2
        simp only [hg]
        refine (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans ?_)
        rw [natDegree_comp, binomPoly_natDegree, natDegree_X_add_C, mul_one]
        omega
      refine (degree_le_of_natDegree_le hnat).trans_lt ?_
      exact_mod_cast (by omega : K - 1 < K)

lemma quotCoeff_VG (p : ℕ) [Fact p.Prime] (n a b k : ℕ) : VG p (quotCoeff n a b k) 0 :=
  newtonCoeff_VG p _ 0 k fun i _ => by
    have := pab_eval_int p n a b (-((4*n : ℕ) : ℤ) + i)
    push_cast at this ⊢
    exact this

lemma inv_choose_VG (p : ℕ) [hp : Fact p.Prime] {k K N : ℕ} (hk : K ≤ k) (hkN : k ≤ N) :
    VG p (((k.choose K : ℚ))⁻¹) (-(Nat.log p N : ℚ)) := by
  have hc : k.choose K ≠ 0 := (Nat.choose_pos hk).ne'
  apply VG.inv (by exact_mod_cast hc)
  rw [padicValRat.of_nat, ← Nat.factorization_def _ hp.out]
  exact_mod_cast (Nat.factorization_choose_le_log).trans (Nat.log_mono_right hkN)

/-- Every integer value of the quotient has v_p >= -log_p N. -/
theorem gramQuot_eval_VG (p : ℕ) [Fact p.Prime] (n a b : ℕ) (m : ℤ) :
    VG p ((gramNum n a b /ₘ D (4*n)).eval (m:ℚ)) (-(Nat.log p (3*n+a+b) : ℚ)) := by
  rw [gramNum_divByMonic, eval_finset_sum]
  apply VG.sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  rw [eval_mul, eval_C]
  have h := ((quotCoeff_VG p n a b k).mul (inv_choose_VG p hk1 (by omega : k ≤ 3*n+a+b))).mul
    (binomPoly_eval_int_VG p (k - 4*n) m)
  simpa using h

theorem gramQuot_natDegree_le (n a b : ℕ) :
    (gramNum n a b /ₘ D (4*n)).natDegree ≤ 3*n+a+b - 4*n := by
  rw [gramNum_divByMonic]
  apply natDegree_sum_le_of_forall_le
  intro k hk
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [binomPoly_natDegree]
  omega

end
end Li2

end
