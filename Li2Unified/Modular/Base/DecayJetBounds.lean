module
public import Li2Unified.Modular.Base.DecayLocal

set_option backward.privateInPublic true

@[expose] public section

/-! support: valuations of order<=2 jets and the bilinear jet
factorisation of localB for the literal binomial Gram numerator.
JGV p P r : coefficients 0,1,2 of P have v_p >= 0,-r,-2r (closed under products). -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def JGV (p : ℕ) (P : ℚ[X]) (r : ℚ) : Prop := ∀ k ≤ 2, VG p (P.coeff k) (-(k:ℚ) * r)

namespace JGV
variable {p : ℕ}

lemma mul [Fact p.Prime] {P Q : ℚ[X]} {r : ℚ} (hP : JGV p P r) (hQ : JGV p Q r) :
    JGV p (P*Q) r := by
  intro k hk
  rw [coeff_mul]
  apply VG.sum
  intro x hx
  have hs := Finset.mem_antidiagonal.mp hx
  have h := (hP x.1 (by omega)).mul (hQ x.2 (by omega))
  refine h.mono (le_of_eq ?_)
  have : (x.1:ℚ) + x.2 = k := by exact_mod_cast hs
  rw [← this]
  ring

lemma one {r : ℚ} : JGV p 1 r := fun k _ => by
  rcases k with _ | k
  · simpa using (VG.one (p := p))
  · simpa [coeff_one] using VG.zero (p := p) _

lemma prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {P : ι → ℚ[X]} {r : ℚ}
    (h : ∀ i ∈ s, JGV p (P i) r) : JGV p (∏ i ∈ s, P i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : JGV p 1 r)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma pow [Fact p.Prime] {P : ℚ[X]} {r : ℚ} (hP : JGV p P r) (n : ℕ) : JGV p (P^n) r := by
  induction n with
  | zero => simpa using (one : JGV p 1 r)
  | succ n ih => rw [pow_succ]; exact ih.mul hP

end JGV

lemma coeff_two_mul (P Q : ℚ[X]) :
    (P*Q).coeff 2 = P.coeff 0 * Q.coeff 2 + P.coeff 1 * Q.coeff 1 + P.coeff 2 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp
  ring

/-- Taylor jets at -m of a polynomial with integer values. -/
lemma comp_JGV_of_int (p : ℕ) [Fact p.Prime] {f : ℚ[X]} {d : ℕ} (hf : f.natDegree ≤ d)
    (hv : ∀ m : ℤ, VG p (f.eval (m:ℚ)) 0) (m : ℕ) {r : ℚ} (hr : (Nat.log p d : ℚ) ≤ r) :
    JGV p (f.comp (X - C (m:ℚ))) r := by
  intro k hk
  have h := taylor_coeff_VG p hf 0 hv (-(m:ℤ)) hk
  have e : (X + C (((-(m:ℤ)) : ℤ) : ℚ)) = X - C (m:ℚ) := by
    push_cast
    rw [map_neg, sub_eq_add_neg]
  rw [e] at h
  refine h.mono ?_
  have hk0 : (0:ℚ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma binom_JGV (p : ℕ) [Fact p.Prime] (a m : ℕ) {r : ℚ} (hr : (Nat.log p a : ℚ) ≤ r) :
    JGV p ((binomPoly a).comp (X - C (m:ℚ))) r :=
  comp_JGV_of_int p (binomPoly_natDegree a).le (binomPoly_eval_int_VG p a) m hr

lemma shiftBinom_JGV (p : ℕ) [Fact p.Prime] (n m : ℕ) {r : ℚ} (hr : (Nat.log p n : ℚ) ≤ r) :
    JGV p ((shiftBinom n).comp (X - C (m:ℚ))) r :=
  comp_JGV_of_int p (shiftBinom_natDegree n).le (shiftBinom_eval_int p n) m hr

/-! ## Normalised jets of E_{K,m} -/

def epsFactor (m l : ℕ) : ℚ[X] := C (((l:ℚ) - m)⁻¹) * X + 1

lemma Epole_comp_eq {K m : ℕ} :
    (Epole K m).comp (X - C (m:ℚ)) =
      C (eraseProd K m) * ∏ l ∈ (Finset.Icc 1 K).erase m, epsFactor m l := by
  rw [Epole, prod_comp, eraseProd, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  have hlm : (l:ℚ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Finset.ne_of_mem_erase hl)
  rw [add_comp, X_comp, C_comp, epsFactor, mul_add, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ hlm, C_1, one_mul, mul_one, map_sub]
  ring

lemma eps_eq_coeff {K m : ℕ} (hm : m ∈ Finset.Icc 1 K) (k : ℕ) :
    eps K m k = (∏ l ∈ (Finset.Icc 1 K).erase m, epsFactor m l).coeff k := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have he := eraseProd_ne_zero h1 h2
  rw [eps, djet, Epole_comp_eq, coeff_C_mul]
  field_simp

lemma inv_diff_VG (p : ℕ) [Fact p.Prime] {l m N : ℕ} (hlm : l ≠ m) (hl : l ≤ N + 1) (hm : m ≤ N + 1)
    (hl1 : 1 ≤ l) (hm1 : 1 ≤ m) : VG p (((l:ℚ) - m)⁻¹) (-(Nat.log p N : ℚ)) := by
  rcases lt_or_gt_of_ne hlm with h | h
  · have e : ((l:ℚ) - m) = -((m - l : ℕ) : ℚ) := by rw [Nat.cast_sub h.le]; ring
    rw [e, inv_neg]
    exact (VG.inv_nat (p := p) (by omega) (by omega)).neg
  · have e : ((l:ℚ) - m) = ((l - m : ℕ) : ℚ) := by rw [Nat.cast_sub h.le]
    rw [e]
    exact VG.inv_nat (p := p) (by omega) (by omega)

lemma epsFactor_JGV (p : ℕ) [Fact p.Prime] {m l : ℕ} {r : ℚ}
    (hu : VG p (((l:ℚ) - m)⁻¹) (-r)) : JGV p (epsFactor m l) r := by
  intro k hk
  interval_cases k
  · simpa [epsFactor] using (VG.one (p := p))
  · simpa [epsFactor, coeff_X, coeff_one] using hu
  · simpa [epsFactor, coeff_X, coeff_one] using VG.zero (p := p) _

theorem eps_VG (p : ℕ) [Fact p.Prime] {K m N : ℕ} (hm : m ∈ Finset.Icc 1 K) (hKN : K ≤ N + 1)
    {k : ℕ} (hk : k ≤ 2) : VG p (eps K m k) (-(k:ℚ) * (Nat.log p N : ℚ)) := by
  rw [eps_eq_coeff hm]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  refine JGV.prod _ (fun l hl => epsFactor_JGV p ?_) k hk
  obtain ⟨hl, hlK⟩ := Finset.mem_erase.mp hl
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hlK
  exact inv_diff_VG p hl (by omega) (by omega) hl1 h1

/-! ## Bilinear jet factorisation of localB -/

/-- e0 * (the coefficient polynomial of the order-k jet in localB). -/
def bhat (K m : ℕ) : ℕ → ℚ[X]
  | 0 => C (eps K m 1 + (m:ℚ) * (eps K m 1 ^ 2 - eps K m 2) + (m:ℚ) * Cst K) + C (m:ℚ) * X
  | 1 => C (-1 - (m:ℚ) * eps K m 1)
  | 2 => C (m:ℚ)
  | _ => 0

theorem localB_jets (K m : ℕ) (F : ℚ[X]) :
    localB K m F = C (1 / eraseProd K m) *
      (C (djet F m 0) * bhat K m 0 + C (djet F m 1) * bhat K m 1 + C (djet F m 2) * bhat K m 2) := by
  unfold localB localC dres
  rw [← djet_zero_eq]
  simp only [bhat, div_eq_mul_inv, map_add, map_mul, map_sub, map_neg, map_one, map_pow, one_mul]
  ring

/-- The matrix coefficient kappa(s,s') at node m (with the K!/e0 factor folded in). -/
def kap (n m : ℕ) (s s' : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range 3, if i + s + s' ≤ 2 then
    C (((4*n).factorial : ℚ) / eraseProd (4*n) m *
        ((shiftBinom n ^ 3).comp (X - C (m:ℚ))).coeff i) * bhat (4*n) m (i + s + s')
    else 0

theorem localB_gram (n m a b : ℕ) :
    localB (4*n) m (gramNum n a b) = ∑ s ∈ Finset.range 3, ∑ s' ∈ Finset.range 3,
      C (djet (binomPoly a) m s) * kap n m s s' * C (djet (binomPoly b) m s') := by
  rw [localB_jets]
  have hg : ∀ k, djet (gramNum n a b) m k = ((4*n).factorial : ℚ) *
      (((shiftBinom n ^ 3).comp (X - C (m:ℚ)) * (binomPoly a).comp (X - C (m:ℚ))) *
        (binomPoly b).comp (X - C (m:ℚ))).coeff k := by
    intro k
    rw [gramNum_eq, djet_C_mul, pab, djet, mul_comp, mul_comp]
  simp only [hg, coeff_two_mul, coeff_one_mul, mul_coeff_zero]
  simp only [kap, djet, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [div_eq_mul_inv]
  ring

/-- For 1 <= m <= n every order<=2 jet of the Gram numerator vanishes. -/
lemma shiftBinom_root {n m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ n) : (shiftBinom n).eval (-(m:ℚ)) = 0 := by
  rw [shiftBinom, eval_comp, eval_add, eval_X, eval_C,
    show -(m:ℚ) + n = ((n - m : ℕ) : ℚ) by rw [Nat.cast_sub h2]; ring,
    binomPoly_eval_nat, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

theorem localB_gram_low {n m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ n) (a b : ℕ) :
    localB (4*n) m (gramNum n a b) = 0 := by
  have hdvd : X - C (-(m:ℚ)) ∣ shiftBinom n := dvd_iff_isRoot.mpr (shiftBinom_root h1 h2)
  obtain ⟨T, hT⟩ := hdvd
  have hS : (shiftBinom n ^ 3).comp (X - C (m:ℚ)) = X^3 * (T.comp (X - C (m:ℚ)))^3 := by
    rw [hT, pow_comp, mul_comp, sub_comp, X_comp, C_comp, map_neg, sub_neg_eq_add, sub_add_cancel]
    ring
  have hz : ∀ k ≤ 2, djet (gramNum n a b) m k = 0 := by
    intro k hk
    rw [gramNum_eq, djet_C_mul, pab, djet, mul_comp, mul_comp, hS, mul_assoc, mul_assoc,
      coeff_X_pow_mul', if_neg (by omega), mul_zero]
  rw [localB_jets, hz 0 (by omega), hz 1 (by omega), hz 2 le_rfl]
  simp

end
end Li2

end
