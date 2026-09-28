module
public import Li2Unified.Modular.Positive.Packed.P041
public import Li2Unified.Modular.Base.DecayFallback
public import Li2Unified.Modular.Positive.Packed.P019
public import Li2Unified.Modular.Positive.Packed.P036
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime
public import Li2Unified.Modular.Positive.Packed.P040

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- Uniform denominator bound for the actual simple-pole value of the parameter family. -/
theorem parameterTau_VG_log (p : ℕ) [Fact p.Prime] (lam : ℚ)
    (hlam : Li2.VG p lam 0) {j N : ℕ} (hjN : j ≤ N) :
    Li2.VG p (Li2.parameterTau lam j) (-2 * (Nat.log p N : ℚ)) := by
  unfold Li2.parameterTau
  apply Li2.VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have h1 : Li2.VG p (lam^a) 0 := by simpa using hlam.pow a
  have h2 := Li2.VG.inv_nat (p := p) (j := a) (n := N) ha1 (ha2.trans hjN)
  have h3 : Li2.VG p (((a:ℚ)^2)⁻¹) (2 * -(Nat.log p N : ℚ)) := by
    rw [← inv_pow]
    exact_mod_cast h2.pow 2
  rw [div_eq_mul_inv]
  refine (h1.mul h3).mono ?_
  linarith

/-- The polynomial part uses precisely the parameter functional from `numeratorFunctional`. -/
theorem parameterU_VG_of_integer_values (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1) (hratio : Li2.VG p (lam/(1-lam)) 0)
    {q : ℚ[X]} {e : ℕ} (hq : q.natDegree ≤ e) (r : ℚ)
    (hv : ∀ m : ℤ, Li2.VG p (q.eval (m:ℚ)) r) :
    Li2.VG p (Li2.parameterU lam q) (r - (Nat.log p e : ℚ)) := by
  unfold Li2.parameterU
  have hdeg : (derivative (X * q)).natDegree ≤ e := by
    refine (natDegree_derivative_le _).trans ?_
    have hm := natDegree_mul_le (p := (X:ℚ[X])) (q := q)
    rw [natDegree_X] at hm
    omega
  apply parameterG_VG_of_integral_ratio p lam h1 hratio hdeg
  intro i _
  have hd := Li2.derivative_eval_VG p hq r hv (i : ℤ)
  rw [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X]
  have hq' : Li2.VG p (q.eval (i:ℚ)) (r - (Nat.log p e : ℚ)) := by
    have := hv (i : ℤ)
    push_cast at this
    exact this.mono (by have := (Nat.cast_nonneg (Nat.log p e) : (0:ℚ) ≤ _); linarith)
  push_cast at hd
  simpa using hq'.add ((Li2.VG.natCast (p := p) i).mul hd |>.mono (by simp))

/-- Good-prime bound for every entry of the original parameter-family Gram matrix. -/
theorem binomGram_entry_GV_good_fallback (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1) (hratio : Li2.VG p (lam/(1-lam)) 0)
    (hlam : Li2.VG p lam 0) (hinv : Li2.VG p lam⁻¹ 0)
    {n : ℕ} (hn : 1 ≤ n) {a b : ℕ} (ha : a < 2*n) (hb : b < 2*n) :
    Li2.GV p (ParameterFamily.numeratorFunctional lam (4*n) (Li2.gramNum n a b))
      (-2 * (Nat.log p (7*n-2) : ℚ)) := by
  set L := (Nat.log p (7*n-2) : ℚ) with hL
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have l1 : (Nat.log p (3*n+a+b) : ℚ) ≤ L := by
    rw [hL]
    exact_mod_cast Nat.log_mono_right (by omega)
  have l2 : (Nat.log p (3*n+a+b-4*n) : ℚ) ≤ L := by
    rw [hL]
    exact_mod_cast Nat.log_mono_right (by omega)
  unfold ParameterFamily.numeratorFunctional
  apply Li2.GV.add
  · apply Li2.GV.C
    set q := Li2.gramNum n a b /ₘ Li2.D (4*n)
    have hq : q.natDegree ≤ 3*n+a+b-4*n := Li2.gramQuot_natDegree_le n a b
    have hu := parameterU_VG_of_integer_values p lam h1 hratio hq
      (-(Nat.log p (3*n+a+b) : ℚ))
      (fun i => by
        have hi := Li2.gramQuot_eval_VG p n a b i
        push_cast at hi
        exact hi)
    exact hu.mono (by linarith)
  · apply Li2.GV.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : Li2.VG p ((Li2.gramNum n a b).eval (-(j:ℚ)) /
        ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))) 0 :=
      Li2.gramRes_VG p n a b hj1 hj2
    have hc : Li2.VG p ((j:ℚ)*lam⁻¹^j) 0 := by
      simpa using (Li2.VG.natCast (p := p) j).mul (hinv.pow j)
    have ht : Li2.VG p (Li2.parameterTau lam j) (-2 * L) :=
      parameterTau_VG_log p lam hlam (by omega : j ≤ 7*n-2)
    have hlin : Li2.GV p (X - C (Li2.parameterTau lam j)) (-2 * L) :=
      (Li2.GV.X.mono (by linarith)).sub (Li2.GV.C ht)
    refine ((Li2.GV.C hres).mul ((Li2.GV.C hc).mul hlin)).mono ?_
    linarith

/-- The good-prime fallback for the unchanged original `Qtilde` at any unit parameter. -/
theorem Qtilde_GV_good_fallback (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1) (hratio : Li2.VG p (lam/(1-lam)) 0)
    (hlam : Li2.VG p lam 0) (hinv : Li2.VG p lam⁻¹ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    Li2.GV p (ParameterFamily.Qtilde lam n)
      (-4 * (n:ℚ) * (Nat.log p (7*n-2) : ℚ)) := by
  set L := (Nat.log p (7*n-2) : ℚ)
  rw [ParameterFamily.Qtilde_eq_binomGram_det]
  have hdet := Li2.det_GV (p := p) (ParameterFamily.binomGram lam n)
    (fun _ => -L) (fun _ => -L) (fun a b => by
      change Li2.GV p (ParameterFamily.numeratorFunctional lam (4*n)
        (Li2.gramNum n a b)) (-L + -L)
      refine (binomGram_entry_GV_good_fallback p lam h1 hratio hlam hinv hn
        a.isLt b.isLt).mono (le_of_eq ?_)
      ring)
  refine hdet.mono (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameterTau_VG_log
#print axioms Li2Unified.Proofs.Arithmetic.parameterU_VG_of_integer_values
#print axioms Li2Unified.Proofs.Arithmetic.binomGram_entry_GV_good_fallback
#print axioms Li2Unified.Proofs.Arithmetic.Qtilde_GV_good_fallback

end

section
/-! Finite prime-factor exclusion for rational block-constant values.
This does not identify those values with the original matrix determinants. -/
namespace Li2Unified.ParameterFamily
noncomputable section

lemma prime_not_dvd_prime_product (p : ℕ) (hp : p.Prime) (qs : List ℕ)
    (hq : ∀ q ∈ qs, q.Prime) (hne : ∀ q ∈ qs, p ≠ q) : ¬p ∣ qs.prod := by
  induction qs with
  | nil => simpa using hp.not_dvd_one
  | cons q qs ih =>
    have hqprime := hq q (by simp)
    have hnq : ¬p ∣ q := by
      rw [Nat.dvd_prime hqprime]
      rintro (h | h)
      · exact hp.ne_one h
      · exact hne q (by simp) h
    apply hp.not_dvd_mul hnq
    exact ih (fun r hr => hq r (by simp [hr])) (fun r hr => hne r (by simp [hr]))

lemma neg_fraction_unit (p a b : ℕ) [Fact p.Prime]
    (ha : 0 < a) (hb : 0 < b) (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) :
    -(a:ℚ)/(b:ℚ) ≠ 0 ∧ padicValRat p (-(a:ℚ)/(b:ℚ)) = 0 := by
  have ha0 : (a:ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb0 : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨div_ne_zero (neg_ne_zero.mpr ha0) hb0, ?_⟩
  rw [padicValRat.div (neg_ne_zero.mpr ha0) hb0, padicValRat.neg,
    nat_valuation_zero a hpa, nat_valuation_zero b hpb, sub_self]

lemma prime_not_dvd_product_outside (p : ℕ) (hp : p.Prime) (bad : Finset ℕ)
    (hbad : p ∉ bad) (qs : List ℕ) (hq : ∀ q ∈ qs, q.Prime)
    (hsub : ∀ q ∈ qs, q ∈ bad) : ¬p ∣ qs.prod :=
  prime_not_dvd_prime_product p hp qs hq (fun q hq he => hbad (he.symm ▸ hsub q hq))

end
end Li2Unified.ParameterFamily

end

section
/-! Exact preparation for lambda=1/2. Constants are formula values;
no original block determinant, Gaussian bound or unconditional Main is claimed. -/
open Polynomial
namespace Li2Unified.Instances.PosHalf
noncomputable section
open Li2Unified.ParameterFamily

def lambda : ℚ := 1/2
def badPrimes : Finset ℕ := {2,3,5,11,2399}
def value : ℝ := r lambda
def Q (n : ℕ) : ℚ[X] := ParameterFamily.Q lambda n
def Qtilde (n : ℕ) : ℚ[X] := ParameterFamily.Qtilde lambda n
def P (n : ℕ) : ℤ[X] := ParameterFamily.P lambda n

lemma lambda_eq_inverse : lambda = inverseParameter 2 := by norm_num [lambda, inverseParameter]
lemma lambda_pos : 0 < lambda := by norm_num [lambda]
lemma lambda_abs_lt_one : |(lambda : ℝ)| < 1 := by norm_num [lambda]
lemma lambda_nonzero : lambda ≠ 0 := lambda_pos.ne'
lemma lambda_ne_one : lambda ≠ 1 := by norm_num [lambda]
lemma numerator_denominator_coprime : Nat.Coprime 1 2 := by norm_num
lemma badPrimes_prime (p : ℕ) (hp : p ∈ badPrimes) : p.Prime := by
  simp only [badPrimes, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma value_eq_series : value =
    ∑' k : ℕ, (1/2:ℝ)^(k+1)/((k:ℝ)+1)^2 := by norm_num [value, r, lambda]
lemma summable_series : Summable (fun k : ℕ => (1/2:ℝ)^(k+1)/((k:ℝ)+1)^2) := by
  simpa only [lambda, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using summable_r lambda lambda_abs_lt_one
lemma Q_natDegree_le (n : ℕ) : (Q n).natDegree ≤ 2*n := ParameterFamily.Q_natDegree_le lambda n
lemma P_natDegree_le (n : ℕ) : (P n).natDegree ≤ 2*n := ParameterFamily.P_natDegree_le lambda n
lemma P_isPrimitive (n : ℕ) (hn : Q n ≠ 0) : (P n).IsPrimitive :=
  ParameterFamily.P_isPrimitive lambda n hn
lemma P_same_Q (n : ℕ) : (P n).map (algebraMap ℤ ℚ) = C (d lambda n) * Q n :=
  P_eq_d_Q lambda n
lemma P_scale_pos (n : ℕ) : 0 < d lambda n := d_pos lambda n
lemma lowBlockConstant_value : lowBlockConstant lambda = -275/2 := by norm_num [lowBlockConstant, lambda]
lemma cornerBlockConstant_value : cornerBlockConstant lambda = -28788 := by norm_num [cornerBlockConstant, lambda]
lemma lowBlockConstant_ne_zero : lowBlockConstant lambda ≠ 0 := by rw [lowBlockConstant_value]; norm_num
lemma cornerBlockConstant_ne_zero : cornerBlockConstant lambda ≠ 0 := by rw [cornerBlockConstant_value]; norm_num

lemma good_prime_inputs (p : ℕ) (hp : p.Prime) (hbad : p ∉ badPrimes) :
    ¬p ∣ 2 ∧ ¬p ∣ 1 := by
  constructor
  · intro hd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> (try norm_num at hp) <;> norm_num [badPrimes] at hbad
  · intro hd
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> (try norm_num at hp) <;> norm_num [badPrimes] at hbad

lemma parameter_units (p : ℕ) [hp : Fact p.Prime] (hbad : p ∉ badPrimes) :
    (lambda ≠ 0 ∧ padicValRat p lambda = 0) ∧
    (1-lambda ≠ 0 ∧ padicValRat p (1-lambda) = 0) ∧
    (lambda^p ≠ 0 ∧ padicValRat p (lambda^p) = 0) ∧
    (1-lambda^p ≠ 0 ∧ padicValRat p (1-lambda^p) = 0) := by
  obtain ⟨hq,hm⟩ := good_prime_inputs p hp.out hbad
  rw [lambda_eq_inverse]
  exact ⟨inverseParameter_unit 2 (by norm_num) hq,
    inverseParameter_one_sub_unit 2 (by norm_num) hq hm,
    inverseParameter_power_unit 2 (by norm_num) hq,
    inverseParameter_power_one_sub_unit 2 (by norm_num) hq hm⟩

lemma parameter_fermat (p : ℕ) [hp : Fact p.Prime] (hbad : p ∉ badPrimes) :
    Li2.VG p (lambda^p-lambda) 1 := by
  rw [lambda_eq_inverse]
  exact inverseParameter_prime_pow_congr 2 (by norm_num) (good_prime_inputs p hp.out hbad).1

lemma moment_integral (p : ℕ) [hp : Fact p.Prime] (hbad : p ∉ badPrimes) :
    Li2.VG p (lambda/(1-lambda)) 0 ∧ Li2.VG p (lambda^p/(1-lambda^p)) 0 := by
  obtain ⟨hq,hm⟩ := good_prime_inputs p hp.out hbad
  rw [lambda_eq_inverse]
  exact ⟨inverseParameter_moment_integral 2 (by norm_num) hq hm,
    inverseParameter_power_moment_integral 2 (by norm_num) hq hm⟩

lemma all_moments_integral (p : ℕ) [Fact p.Prime] (hbad : p ∉ badPrimes) (k : ℕ) :
    Li2.VG p (Li2.parameterMoment lambda k) 0 ∧
      Li2.VG p (Li2.parameterMoment (lambda^p) k) 0 :=
  ⟨Li2.parameterMoment_VG p lambda (moment_integral p hbad).1 k,
    Li2.parameterMoment_VG p (lambda^p) (moment_integral p hbad).2 k⟩

lemma good_prime_not_dvd_275 (p : ℕ) (hp : p.Prime) (hbad : p ∉ badPrimes) : ¬p ∣ 275 := by
  have h := prime_not_dvd_product_outside p hp badPrimes hbad [5,5,11]
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> norm_num [badPrimes])
  norm_num at h
  exact h

lemma good_prime_not_dvd_2 (p : ℕ) (hp : p.Prime) (hbad : p ∉ badPrimes) : ¬p ∣ 2 := by
  have h := prime_not_dvd_product_outside p hp badPrimes hbad [2]
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl <;> norm_num)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl <;> norm_num [badPrimes])
  norm_num at h
  exact h

lemma good_prime_not_dvd_28788 (p : ℕ) (hp : p.Prime) (hbad : p ∉ badPrimes) : ¬p ∣ 28788 := by
  have h := prime_not_dvd_product_outside p hp badPrimes hbad [2,2,3,2399]
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> norm_num)
    (by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> norm_num [badPrimes])
  norm_num at h
  exact h

lemma good_prime_not_dvd_1 (p : ℕ) (hp : p.Prime) (hbad : p ∉ badPrimes) : ¬p ∣ 1 := by
  exact hp.not_dvd_one

lemma lowBlockConstant_unit (p : ℕ) [hp : Fact p.Prime] (hbad : p ∉ badPrimes) :
    lowBlockConstant lambda ≠ 0 ∧ padicValRat p (lowBlockConstant lambda) = 0 := by
  rw [lowBlockConstant_value]
  simpa using neg_fraction_unit p 275 2 (by norm_num) (by norm_num)
    (good_prime_not_dvd_275 p hp.out hbad) (good_prime_not_dvd_2 p hp.out hbad)

lemma cornerBlockConstant_unit (p : ℕ) [hp : Fact p.Prime] (hbad : p ∉ badPrimes) :
    cornerBlockConstant lambda ≠ 0 ∧ padicValRat p (cornerBlockConstant lambda) = 0 := by
  rw [cornerBlockConstant_value]
  simpa using neg_fraction_unit p 28788 1 (by norm_num) (by norm_num)
    (good_prime_not_dvd_28788 p hp.out hbad) (good_prime_not_dvd_1 p hp.out hbad)

end
end Li2Unified.Instances.PosHalf

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Filter Finset

/-- All positive-half primes at least five satisfy the uniform logarithmic
fallback before any medium-prime profile estimate is used. -/
theorem posHalf_goodPrime_fallback (n p : ℕ) (hn : 1 ≤ n)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    Li2.GV p (Instances.PosHalf.Qtilde n)
      (-4*(n:ℚ)*(Nat.log p (7*n-2):ℚ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hp1 : ¬ p ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    omega
  have hu := inverseParameter_unit (p := p) 2 (by norm_num) hp2
  have hlam : Li2.VG p lambda 0 := by
    rw [lambda_eq_inverse]
    right
    rw [hu.2]
    norm_num
  have hinv : Li2.VG p lambda⁻¹ 0 := by
    rw [lambda_eq_inverse]
    exact Li2.rational_unit_inverse_VG (inverseParameter 2) hu.1 hu.2
  have hratio : Li2.VG p (lambda/(1-lambda)) 0 := by
    rw [lambda_eq_inverse]
    exact inverseParameter_moment_integral 2 (by norm_num) hp2 hp1
  exact Qtilde_GV_good_fallback p lambda lambda_ne_one
    hratio hlam hinv hn

/-- The actual primitive content dominates the small-prime fallback at a
fixed cutoff. -/
theorem posHalf_smallTail_sum_lower (δ : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hne : Instances.PosHalf.Qtilde n ≠ 0) :
    smallTailFallbackBound δ n ≤
      ∑ p ∈ smallTailPrimes δ n,
        if p.Prime then
          ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
        else 0 := by
  unfold smallTailFallbackBound
  apply Finset.sum_le_sum
  intro p hpS
  have hpr : p.Prime := (Finset.mem_filter.mp hpS).2
  have hp5 : 5 ≤ p := by
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hpS).1).1
    omega
  letI : Fact p.Prime := ⟨hpr⟩
  have hq := posHalf_goodPrime_fallback n p hn hpr hp5
  have hv : (-4*(n:ℝ)*(Nat.log p (7*n-2):ℝ)) ≤
      ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ) := by
    exact_mod_cast parameter_dtilde_GV_lower lambda n p hne hq
  have hlog : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
  simpa [hpr] using mul_le_mul_of_nonneg_right hv hlog

/-- At cutoff `1/200`, the small primes cost at most `4/200 + ε` in the
quadratic exponent. -/
theorem posHalf_smallTail_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      ((-4/200:ℝ)-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ smallTailPrimes (1/200:ℝ) n,
          if p.Prime then
            ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
          else 0 := by
  have hmass : ∀ᶠ n : ℕ in atTop,
      (-4/200:ℝ)-ε ≤
        smallTailFallbackBound (1/200:ℝ) n/(n:ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith)
      (smallTailFallbackBound_tendsto (1/200:ℝ) (by norm_num) (by norm_num))
  filter_upwards [hmass, eventually_ge_atTop (1:ℕ)] with n hm hn
  intro hne
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hcost : ((-4/200:ℝ)-ε)*(n:ℝ)^2 ≤
      smallTailFallbackBound (1/200:ℝ) n :=
    (le_div_iff₀ (sq_pos_of_pos hnpos)).mp hm
  exact hcost.trans (posHalf_smallTail_sum_lower (1/200:ℝ) n hn hne)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_goodPrime_fallback
#print axioms Li2Unified.Proofs.Arithmetic.posHalf_smallTail_sum_lower
#print axioms Li2Unified.Proofs.Arithmetic.posHalf_smallTail_eventually

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Filter

/-- The actual small-prime fallback works for every fixed positive cutoff. -/
theorem posHalf_smallTail_eventually_delta (δ ε : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Instances.PosHalf.Qtilde n ≠ 0 →
      (-4*δ-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ smallTailPrimes δ n,
          if p.Prime then
            ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
          else 0 := by
  have hmass : ∀ᶠ n : ℕ in atTop,
      -4*δ-ε ≤ smallTailFallbackBound δ n/(n:ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith)
      (smallTailFallbackBound_tendsto δ hδ0 hδ1)
  filter_upwards [hmass, eventually_ge_atTop (1:ℕ)] with n hm hn
  intro hne
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hcost : (-4*δ-ε)*(n:ℝ)^2 ≤ smallTailFallbackBound δ n :=
    (le_div_iff₀ (sq_pos_of_pos hnpos)).mp hm
  exact hcost.trans (posHalf_smallTail_sum_lower δ n hn hne)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_smallTail_eventually_delta

end


end
