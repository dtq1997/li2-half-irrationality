module
public import Li2Unified.Modular.Base.DecayReflect
public import Li2Unified.Modular.Base.DecayPoleSplit
public import Li2Unified.Modular.Base.PoleFamily

set_option backward.privateInPublic true

@[expose] public section

/-! exact finite reflected representation of the literal
functional numeratorFunctional K. For every F,
  L(F) = -F(0)/K! + sum_{m=1}^K (-2)^m B_m(F) + tail(F),
where B_m(F) depends only on the Taylor coefficients of order 0,1,2 of F at -m
(`localC`, built from `djet`), and tail(F) is an explicit finite expression.
The identity is exact in ℚ[X]; no 2-adic limit is taken. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def Epole (K m : ℕ) : ℚ[X] := ∏ l ∈ (Finset.Icc 1 K).erase m, (X + C (l:ℚ))

def dres (K : ℕ) (F : ℚ[X]) (j : ℕ) : ℚ := F.eval (-(j:ℚ)) / eraseProd K j

lemma D_eq_mul_Epole {K m : ℕ} (hm : m ∈ Finset.Icc 1 K) :
    D K = (X + C (m:ℚ)) * Epole K m := by
  rw [D, Epole, Finset.mul_prod_erase _ (fun l : ℕ => X + C (l:ℚ)) hm]

theorem decay_partial_fractions (K : ℕ) (F : ℚ[X]) :
    F = (F /ₘ D K) * D K + ∑ j ∈ Finset.Icc 1 K, C (dres K F j) * Epole K j := by
  have h := SimplePoles.partial_fractionsP F (negativePoles K)
  rw [SimplePoles.polyPart, negativePoles_product] at h
  conv_lhs => rw [h]
  congr 1
  unfold negativePoles
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    have hres : SimplePoles.resP F ((Finset.Icc 1 K).image (fun j:ℕ => -(j:ℤ))) (-(j:ℤ)) =
        dres K F j := by
      unfold SimplePoles.resP dres eraseProd
      rw [← Finset.image_erase negative_nat_injective, Finset.prod_image]
      · simp only [Int.cast_neg, Int.cast_natCast, neg_sub_neg]
      · intro a _ b _ h
        exact negative_nat_injective h
    rw [hres, Epole, ← Finset.image_erase negative_nat_injective, Finset.prod_image]
    · simp only [Int.cast_neg, Int.cast_natCast, C_neg, sub_neg_eq_add]
    · intro a _ b _ he
      exact negative_nat_injective he
  · intro a _ b _ he
    exact negative_nat_injective he

/-! ## Jets at -m -/

def djet (F : ℚ[X]) (m k : ℕ) : ℚ := (F.comp (X - C (m:ℚ))).coeff k

lemma djet_add (F G : ℚ[X]) (m k : ℕ) : djet (F+G) m k = djet F m k + djet G m k := by
  simp [djet, add_comp]

lemma djet_C_mul (c : ℚ) (F : ℚ[X]) (m k : ℕ) : djet (C c * F) m k = c * djet F m k := by
  simp [djet, mul_comp, C_comp, coeff_C_mul]

lemma djet_sum {ι : Type*} (s : Finset ι) (F : ι → ℚ[X]) (m k : ℕ) :
    djet (∑ i ∈ s, F i) m k = ∑ i ∈ s, djet (F i) m k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [djet]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, djet_add, ih]

lemma djet_zero_eq (F : ℚ[X]) (m : ℕ) : djet F m 0 = F.eval (-(m:ℚ)) := by
  simp [djet, coeff_zero_eq_eval_zero, eval_comp]

lemma djet_one_eq (F : ℚ[X]) (m : ℕ) : djet F m 1 = (derivative F).eval (-(m:ℚ)) := by
  have h1 : (F.comp (X - C (m:ℚ))).coeff 1 = (derivative (F.comp (X - C (m:ℚ)))).eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp
  rw [djet, h1, derivative_comp]
  simp [eval_comp]

lemma coeff_one_mul (P Q : ℚ[X]) :
    (P*Q).coeff 1 = P.coeff 0 * Q.coeff 1 + P.coeff 1 * Q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

lemma Epole_djet_zero (K m : ℕ) : djet (Epole K m) m 0 = eraseProd K m := by
  rw [djet_zero_eq, Epole, eval_prod, eraseProd]
  apply Finset.prod_congr rfl
  intro l _
  simp
  ring

/-! ## The local constant -/

def eps (K m k : ℕ) : ℚ := djet (Epole K m) m k / eraseProd K m

def localC (K m : ℕ) (F : ℚ[X]) : ℚ :=
  (djet F m 0 * (eps K m 1 + (m:ℚ) * (eps K m 1 ^ 2 - eps K m 2)) +
    djet F m 1 * (-1 - (m:ℚ) * eps K m 1) + djet F m 2 * (m:ℚ)) / eraseProd K m

lemma localC_add (K m : ℕ) (F G : ℚ[X]) : localC K m (F+G) = localC K m F + localC K m G := by
  unfold localC
  rw [djet_add, djet_add, djet_add]
  ring

lemma localC_C_mul (K m : ℕ) (c : ℚ) (F : ℚ[X]) : localC K m (C c * F) = c * localC K m F := by
  unfold localC
  rw [djet_C_mul, djet_C_mul, djet_C_mul]
  ring

lemma localC_sum {ι : Type*} (K m : ℕ) (s : Finset ι) (F : ι → ℚ[X]) :
    localC K m (∑ i ∈ s, F i) = ∑ i ∈ s, localC K m (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := localC_C_mul K m 0 0
    simpa using h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, localC_add, ih]

lemma localC_Epole_self {K m : ℕ} (hm : m ∈ Finset.Icc 1 K) : localC K m (Epole K m) = 0 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have he := eraseProd_ne_zero h1 h2
  unfold localC eps
  rw [Epole_djet_zero]
  field_simp
  ring

lemma localC_qD {K m : ℕ} (hm : m ∈ Finset.Icc 1 K) (q : ℚ[X]) :
    localC K m (q * D K) = -(q.eval (-(m:ℚ))) + (m:ℚ) * (derivative q).eval (-(m:ℚ)) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have he := eraseProd_ne_zero h1 h2
  have hcomp : (q * D K).comp (X - C (m:ℚ)) =
      X * ((q.comp (X - C (m:ℚ))) * ((Epole K m).comp (X - C (m:ℚ)))) := by
    rw [D_eq_mul_Epole hm, mul_comp, mul_comp, add_comp, X_comp, C_comp, sub_add_cancel]
    ring
  have j0 : djet (q * D K) m 0 = 0 := by
    rw [djet, hcomp, coeff_X_mul_zero]
  have j1 : djet (q * D K) m 1 = djet q m 0 * eraseProd K m := by
    rw [djet, hcomp, coeff_X_mul, mul_coeff_zero, ← Epole_djet_zero]
    rfl
  have j2 : djet (q * D K) m 2 = djet q m 0 * djet (Epole K m) m 1 +
      djet q m 1 * eraseProd K m := by
    rw [djet, hcomp, coeff_X_mul, coeff_one_mul, ← Epole_djet_zero]
    rfl
  unfold localC eps
  rw [j0, j1, j2, djet_zero_eq q m, djet_one_eq q m]
  field_simp
  ring

lemma coeff_mul_X_add_C_zero (P : ℚ[X]) (c : ℚ) : (P * (X + C c)).coeff 0 = P.coeff 0 * c := by
  simp [mul_add, coeff_C]

lemma coeff_mul_X_add_C_succ (P : ℚ[X]) (c : ℚ) (k : ℕ) :
    (P * (X + C c)).coeff (k+1) = P.coeff k + P.coeff (k+1) * c := by
  rw [mul_add, coeff_add, coeff_mul_X, coeff_mul_C]

lemma localC_Epole_other {K m j : ℕ} (hm : m ∈ Finset.Icc 1 K) (hj : j ∈ Finset.Icc 1 K)
    (hjm : j ≠ m) : localC K m (Epole K j) = -((j:ℚ) / ((j:ℚ) - m)^2) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have he := eraseProd_ne_zero h1 h2
  have hc : (j:ℚ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hjm)
  have hrel : (Epole K j).comp (X - C (m:ℚ)) * (X + C ((j:ℚ) - m)) =
      X * (Epole K m).comp (X - C (m:ℚ)) := by
    have hD : Epole K j * (X + C (j:ℚ)) = (X + C (m:ℚ)) * Epole K m := by
      rw [mul_comm, ← D_eq_mul_Epole hj, D_eq_mul_Epole hm]
    have := congrArg (fun P => P.comp (X - C (m:ℚ))) hD
    simp only [mul_comp, add_comp, X_comp, C_comp] at this
    rw [sub_add_cancel] at this
    rw [← this, map_sub]
    ring
  set u := fun k => djet (Epole K j) m k with hu
  set e := fun k => djet (Epole K m) m k with he'
  have c0 := Polynomial.ext_iff.mp hrel 0
  have c1 := Polynomial.ext_iff.mp hrel 1
  have c2 := Polynomial.ext_iff.mp hrel 2
  simp only [coeff_mul_X_add_C_zero, coeff_X_mul_zero] at c0
  rw [show (1:ℕ) = 0 + 1 from rfl, coeff_mul_X_add_C_succ, coeff_X_mul] at c1
  rw [show (2:ℕ) = 1 + 1 from rfl, coeff_mul_X_add_C_succ, coeff_X_mul] at c2
  change u 0 * ((j:ℚ) - m) = 0 at c0
  change u 0 + u 1 * ((j:ℚ) - m) = e 0 at c1
  change u 1 + u 2 * ((j:ℚ) - m) = e 1 at c2
  have hu0 : u 0 = 0 := by
    rcases mul_eq_zero.mp c0 with h | h
    · exact h
    · exact absurd h hc
  have he0 : e 0 = eraseProd K m := Epole_djet_zero K m
  have hu1 : u 1 = e 0 / ((j:ℚ) - m) := by
    rw [hu0, zero_add] at c1
    field_simp
    linarith
  have hu2 : u 2 = (e 1 - u 1) / ((j:ℚ) - m) := by
    field_simp
    linarith
  unfold localC eps
  change (u 0 * (e 1 / eraseProd K m + (m:ℚ) * ((e 1 / eraseProd K m) ^ 2 -
      e 2 / eraseProd K m)) + u 1 * (-1 - (m:ℚ) * (e 1 / eraseProd K m)) + u 2 * (m:ℚ)) /
      eraseProd K m = _
  rw [hu2, hu1, hu0, he0]
  field_simp
  ring

/-- **Local identity** at a pole node m in [1,K], for every F. -/
theorem localC_eq {K m : ℕ} (hm : m ∈ Finset.Icc 1 K) (F : ℚ[X]) :
    localC K m F = -((F /ₘ D K).eval (-(m:ℚ))) + (m:ℚ) * (derivative (F /ₘ D K)).eval (-(m:ℚ)) -
      ∑ j ∈ Finset.Icc 1 K, dres K F j * ((j:ℚ) / ((j:ℚ) - m)^2) := by
  conv_lhs => rw [decay_partial_fractions K F]
  rw [localC_add, localC_sum, localC_qD hm, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [localC_C_mul]
  by_cases hjm : j = m
  · subst hjm
    rw [localC_Epole_self hm]
    simp
  · rw [localC_Epole_other hm hj hjm]
    ring

lemma Epole_eval_zero {K j : ℕ} (hj : j ∈ Finset.Icc 1 K) :
    (j:ℚ) * (Epole K j).eval 0 = (K.factorial : ℚ) := by
  have h := congrArg (eval 0) (D_eq_mul_Epole hj)
  rw [eval_mul, eval_add, eval_X, eval_C, zero_add] at h
  rw [← h]
  have := D_eval_nat K 0
  simpa using this

theorem eval_zero_rep (K : ℕ) (F : ℚ[X]) :
    F.eval 0 / (K.factorial : ℚ) = (F /ₘ D K).eval 0 +
      ∑ j ∈ Finset.Icc 1 K, dres K F j * poleNode j 0 := by
  have hK : (K.factorial : ℚ) ≠ 0 := by positivity
  have hD : (D K).eval 0 = (K.factorial : ℚ) := by simpa using D_eval_nat K 0
  have hF : F.eval 0 = (K.factorial : ℚ) * ((F /ₘ D K).eval 0 +
      ∑ j ∈ Finset.Icc 1 K, dres K F j * poleNode j 0) := by
    conv_lhs => rw [decay_partial_fractions K F]
    rw [eval_add, eval_mul, hD, eval_finset_sum, mul_add, Finset.mul_sum]
    congr 1
    · ring
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : (j:ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      exact_mod_cast (by omega : j ≠ 0)
    have hE := Epole_eval_zero hj
    rw [eval_mul, eval_C, poleNode]
    simp only [pow_zero, mul_one, Nat.cast_zero, sub_zero]
    rw [← hE]
    field_simp
  rw [hF, mul_div_assoc, mul_div_cancel₀ _ hK]

/-! ## The reflected representation -/

def gpart (K : ℕ) (F : ℚ[X]) : ℚ[X] := derivative (X * (F /ₘ D K))

lemma gpart_eval (K : ℕ) (F : ℚ[X]) (x : ℚ) :
    (gpart K F).eval x = (F /ₘ D K).eval x + x * (derivative (F /ₘ D K)).eval x := by
  simp [gpart, derivative_mul]

def tailC (K : ℕ) (F : ℚ[X]) : ℚ :=
  (-2:ℚ)^(K+1) * Gm ((gpart K F).comp (X - C ((K+1 : ℕ):ℚ))) -
    ∑ j ∈ Finset.Icc 1 K, dres K F j * ∑ m ∈ Finset.Ico (K+1) (j+K+1), poleNode j m

def localB (K m : ℕ) (F : ℚ[X]) : ℚ[X] :=
  C (localC K m F + (m:ℚ) * dres K F m * Cst K) + C ((m:ℚ) * dres K F m) * X

lemma range_succ_split (f : ℕ → ℚ) (K : ℕ) :
    ∑ m ∈ Finset.range (K+1), f m = f 0 + ∑ m ∈ Finset.Icc 1 K, f m := by
  rw [Finset.sum_range_succ', sum_Icc_one_eq_range]
  ring

theorem reflected_rep (K : ℕ) (F : ℚ[X]) :
    numeratorFunctional K F = C (-(F.eval 0 / (K.factorial : ℚ))) +
      ∑ m ∈ Finset.Icc 1 K, C ((-2:ℚ)^m) * localB K m F + C (tailC K F) := by
  set r := fun j => dres K F j with hr
  set G := gpart K F with hG
  set q := F /ₘ D K with hq
  -- affine form of the left side
  have hA : numeratorFunctional K F =
      C (polynomialMoment q - ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j * tau j)) +
      C (∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j)) * X := by
    unfold numeratorFunctional
    have hterm : ∀ j ∈ Finset.Icc 1 K,
        C (F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 K).erase j, ((l:ℚ)-(j:ℚ))) *
          (C ((j:ℚ)*(-2:ℚ)^j) * (X - C (tau j))) =
        C (r j * ((j:ℚ) * (-2:ℚ)^j)) * X - C (r j * ((j:ℚ) * (-2:ℚ)^j * tau j)) := by
      intro j _
      simp only [hr, dres, eraseProd, map_mul]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
      ← map_sum, map_sub]
    ring
  -- affine form of the right side
  have hB : ∑ m ∈ Finset.Icc 1 K, C ((-2:ℚ)^m) * localB K m F =
      C (∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * (localC K m F + (m:ℚ) * r m * Cst K)) +
      C (∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * ((m:ℚ) * r m)) * X := by
    have hterm : ∀ m ∈ Finset.Icc 1 K, C ((-2:ℚ)^m) * localB K m F =
        C ((-2:ℚ)^m * (localC K m F + (m:ℚ) * r m * Cst K)) +
        C ((-2:ℚ)^m * ((m:ℚ) * r m)) * X := by
      intro m _
      simp only [localB, hr, map_mul]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum]
  rw [hA, hB]
  -- scalar identities
  have hX : ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j) =
      ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * ((m:ℚ) * r m) :=
    Finset.sum_congr rfl fun j _ => by ring
  have hPM : polynomialMoment q = -(G.eval 0 +
      ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * G.eval (-(m:ℚ))) +
      (-2:ℚ)^(K+1) * Gm (G.comp (X - C ((K+1 : ℕ):ℚ))) := by
    rw [polynomialMoment_eq_Gm, Gm_back _ (K+1), range_succ_split]
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero]
    rfl
  have hloc : ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * localC K m F =
      -(∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * G.eval (-(m:ℚ))) -
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Icc 1 K, poleNode j m := by
    have h1 : ∀ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * localC K m F =
        -((-2:ℚ)^m * G.eval (-(m:ℚ))) - ∑ j ∈ Finset.Icc 1 K, r j * poleNode j m := by
      intro m hm
      rw [localC_eq hm, hG, gpart_eval, mul_sub, Finset.mul_sum]
      have hs : ∑ j ∈ Finset.Icc 1 K, (-2:ℚ)^m * (dres K F j * ((j:ℚ) / ((j:ℚ) - m)^2)) =
          ∑ j ∈ Finset.Icc 1 K, r j * poleNode j m :=
        Finset.sum_congr rfl fun j _ => by simp only [hr, poleNode]; ring
      rw [hs]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have h0 : F.eval 0 / (K.factorial : ℚ) = G.eval 0 +
      ∑ j ∈ Finset.Icc 1 K, r j * poleNode j 0 := by
    rw [eval_zero_rep, hG, gpart_eval]
    simp [hr]
  have htau : ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j * tau j) =
      ∑ j ∈ Finset.Icc 1 K, r j * poleNode j 0 +
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Icc 1 K, poleNode j m +
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Ico (K+1) (j+K+1), poleNode j m -
      ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j * Cst K) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hs := pole_split K j
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : K+1 ≤ j+K+1), range_succ_split] at hs
    have : (j:ℚ) * (-2:ℚ)^j * tau j = poleNode j 0 + ∑ m ∈ Finset.Icc 1 K, poleNode j m +
        ∑ m ∈ Finset.Ico (K+1) (j+K+1), poleNode j m - (j:ℚ) * (-2:ℚ)^j * Cst K := by
      linear_combination hs
    rw [this]
    ring
  have hCs : ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * ((m:ℚ) * r m * Cst K) =
      ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j * Cst K) :=
    Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * (localC K m F + (m:ℚ) * r m * Cst K) =
      ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * localC K m F +
      ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * ((m:ℚ) * r m * Cst K) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hT : tailC K F = (-2:ℚ)^(K+1) * Gm (G.comp (X - C ((K+1 : ℕ):ℚ))) -
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Ico (K+1) (j+K+1), poleNode j m := rfl
  rw [hX, hsplit]
  have hscal : polynomialMoment q - ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * (-2:ℚ)^j * tau j) =
      -(F.eval 0 / (K.factorial : ℚ)) +
      (∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * localC K m F +
        ∑ m ∈ Finset.Icc 1 K, (-2:ℚ)^m * ((m:ℚ) * r m * Cst K)) + tailC K F := by
    rw [hPM, hloc, h0, htau, hCs, hT]
    ring
  rw [hscal, map_add, map_add, map_add, map_neg]
  ring

end
end Li2

end
