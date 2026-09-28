module
public import Li2Unified.Modular.Positive.Packed.P001
public import Li2Unified.Modular.Base.MediumClassIndicators
public import Li2Unified.Modular.Base.MediumFloorSum
public import Mathlib.Data.Int.CardIntervalMod

set_option backward.privateInPublic true

@[expose] public section

section
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
open Li2
variable {p : ℕ} [hp : Fact p.Prime]

theorem matchingCount_add_one (K : ℕ) (c : Fin p) :
    matchingCount K p (c+1) = K/p + if c.val < K%p then 1 else 0 := by
  have hp0 : 0 < p := hp.out.pos
  have hcv : (c+1 : Fin p).val = (c.val+1)%p := by
    simp [Fin.val_add, Fin.val_one, Nat.add_mod]
  have hcard : ((Finset.range K).filter (fun j => j ≡ c.val [MOD p])).card =
      ((Finset.Icc 1 K).filter (fun j => j%p = (c+1 : Fin p).val)).card := by
    apply Finset.card_bij (fun j _ => j+1)
    · intro j hj
      obtain ⟨hj, hjc⟩ := Finset.mem_filter.mp hj
      have hjK := Finset.mem_range.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩, ?_⟩
      rw [hcv]
      exact hjc.add_right 1
    · intro a ha b hb hab
      omega
    · intro j hj
      obtain ⟨hj, hjc⟩ := Finset.mem_filter.mp hj
      obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
      refine ⟨j-1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, by omega⟩
      apply Nat.ModEq.add_right_cancel' 1
      change ((j-1)+1)%p = (c.val+1)%p
      rw [show j-1+1 = j by omega, ← hcv]
      exact hjc
  rw [matchingCount, ← hcard, ← Nat.count_eq_card_filter_range]
  simpa [Nat.mod_eq_of_lt c.isLt] using Nat.count_modEq_card K (r := p) hp0 c.val


theorem matchingCount_weighted_sum (n : ℕ) :
    (∑ c : Fin p, ((matchingCount (4*n) p c : ℚ)-2*(matchingCount n p c : ℚ)) *
      ((matchingCount n p c : ℚ)-2)) =
    (p : ℚ)*(((4*n)/p : ℕ)-2*(n/p : ℕ))*((n/p : ℕ)-2) +
    ((4*n/p : ℕ)-4*(n/p : ℕ)+2)*(n%p : ℕ) +
    ((n/p : ℕ)-2)*((4*n)%p : ℕ) + (min (n%p) ((4*n)%p) : ℕ) := by
  let A : ℚ := (n/p : ℕ)
  let L : ℚ := ((4*n)/p : ℕ)
  have hr : n%p ≤ p := (Nat.mod_lt n hp.out.pos).le
  have hs : (4*n)%p ≤ p := (Nat.mod_lt (4*n) hp.out.pos).le
  have hsum := Equiv.sum_comp (Equiv.addRight (1 : Fin p))
    (fun c => ((matchingCount (4*n) p c : ℚ)-2*(matchingCount n p c : ℚ)) *
      ((matchingCount n p c : ℚ)-2))
  rw [← hsum]
  change (∑ c : Fin p, ((matchingCount (4*n) p (c+1) : ℚ)-
    2*(matchingCount n p (c+1) : ℚ))*((matchingCount n p (c+1) : ℚ)-2)) = _
  simp_rw [matchingCount_add_one, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpoint (c : Fin p) :
      ((L + if c.val < (4*n)%p then 1 else 0)-2*(A + if c.val < n%p then 1 else 0)) *
        ((A + if c.val < n%p then 1 else 0)-2) =
      if c.val < n%p then (if c.val < (4*n)%p then (L-2*A-1)*(A-1) else (L-2*A-2)*(A-1))
      else (if c.val < (4*n)%p then (L-2*A+1)*(A-2) else (L-2*A)*(A-2)) := by
    split_ifs <;> ring
  change (∑ c : Fin p, ((L + if c.val < (4*n)%p then 1 else 0)-
    2*(A + if c.val < n%p then 1 else 0))*((A + if c.val < n%p then 1 else 0)-2)) = _
  simp_rw [hpoint]
  rw [sum_fin_two_cuts_rat hr hs]
  dsimp [A,L]
  ring


theorem matchingCount_normalized_sum (n : ℕ) :
    (∑ c : Fin p, ((matchingCount (4*n) p c : ℚ)-2*(matchingCount n p c : ℚ)) *
      ((matchingCount n p c : ℚ)-2)) + ((4*n)/p : ℕ) - 2*(n/p : ℕ) + normVal p n =
    let A : ℚ := (n/p : ℕ)
    let L : ℚ := ((4*n)/p : ℕ)
    let B : ℚ := ((2*n)/p : ℕ)
    (n : ℚ)*(3*L-6*A-4*B-6) +
    (p : ℚ)*(A*(2*A-L+2)+B*(B+1)) +
    min ((n : ℚ)-A*p) (4*(n : ℚ)-L*p) + L-2*A := by
  have hn : ((n%p : ℕ) : ℚ) = (n : ℚ)-(n/p : ℕ)*(p : ℚ) := by
    have ht : ((n%p : ℕ) : ℚ)+(p : ℚ)*(n/p : ℕ) = (n : ℚ) := by
      exact_mod_cast Nat.mod_add_div n p
    linarith
  have h4 : (((4*n)%p : ℕ) : ℚ) = 4*(n : ℚ)-((4*n)/p : ℕ)*(p : ℚ) := by
    have ht : (((4*n)%p : ℕ) : ℚ)+(p : ℚ)*((4*n)/p : ℕ) = ((4*n : ℕ) : ℚ) := by
      exact_mod_cast Nat.mod_add_div (4*n) p
    push_cast at ht
    linarith
  dsimp only
  rw [matchingCount_weighted_sum, normVal_eq_quotients hp.out.pos, Nat.cast_min, hn, h4]
  ring

end
end Li2Unified.Proofs.Hermite
#print axioms Li2Unified.Proofs.Hermite.matchingCount_add_one
#print axioms Li2Unified.Proofs.Hermite.matchingCount_weighted_sum
#print axioms Li2Unified.Proofs.Hermite.matchingCount_normalized_sum

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem matchingCount_le_floor_add_one (n : ℕ) (a : Fin p) :
    matchingCount n p a ≤ n / p + 1 := by
  obtain ⟨c, hc⟩ := (Equiv.addRight (1 : Fin p)).surjective a
  subst a
  change matchingCount n p (c + 1) ≤ n / p + 1
  rw [matchingCount_add_one]
  split_ifs <;> omega

theorem matchingCount_zero (n : ℕ) :
    matchingCount n p (⟨0, (Fact.out : p.Prime).pos⟩ : Fin p) = n / p := by
  rw [matchingCount]
  convert Nat.Ioc_filter_dvd_card_eq_div n p using 1
  congr 1

theorem matchingCount_le_triple_floor (n : ℕ) (hpn : p ≤ n)
    (a : Fin p) : matchingCount n p a ≤ (3 * n) / p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hA : 1 ≤ n / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    simpa using hpn
  have h3 : 3 * (n / p) ≤ (3 * n) / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    nlinarith [Nat.div_mul_le_self n p]
  have hN := matchingCount_le_floor_add_one n a
  omega

#print axioms matchingCount_le_floor_add_one
#print axioms matchingCount_zero
#print axioms matchingCount_le_triple_floor
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem matchingCount_tail_floor (n : ℕ) (c : Fin p) :
    (3 * n) / p + matchingCount n p (c + 1) ≤
      matchingCount (4 * n) p (c + 1) ∧
    matchingCount (4 * n) p (c + 1) ≤
      (3 * n) / p + matchingCount n p (c + 1) + 1 := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hlo : n / p + (3 * n) / p ≤ (4 * n) / p := by
    simpa [show n + 3 * n = 4 * n by omega] using
      (Nat.div_add_div_le_add_div (x := n) (y := 3 * n) (z := p))
  have hrem : n % p + (3 * n) % p + p * (n / p + (3 * n) / p) =
      (4 * n) % p + p * ((4 * n) / p) := by
    nlinarith [Nat.mod_add_div n p, Nat.mod_add_div (3 * n) p,
      Nat.mod_add_div (4 * n) p]
  have hhi : (4 * n) / p ≤ n / p + (3 * n) / p + 1 := by
    by_contra h
    have hq : n / p + (3 * n) / p + 2 ≤ (4 * n) / p := by omega
    have hm := Nat.mul_le_mul_left p hq
    have hr1 := Nat.mod_lt n hp0
    have hr3 := Nat.mod_lt (3 * n) hp0
    have hmul : p * (n / p + (3 * n) / p) + 2 * p ≤
        p * ((4 * n) / p) := by nlinarith only [hm]
    have hlarge : 2 * p ≤ n % p + (3 * n) % p := by omega
    omega
  have hcases : (4 * n) / p = n / p + (3 * n) / p ∨
      (4 * n) / p = n / p + (3 * n) / p + 1 := by omega
  rcases hcases with hq | hq
  · have hr : n % p ≤ (4 * n) % p := by
      rw [hq] at hrem
      omega
    simp only [matchingCount_add_one]
    split_ifs <;> omega
  · have hs : (3 * n) % p < p := Nat.mod_lt _ hp0
    have hr : (4 * n) % p < n % p := by
      rw [hq] at hrem
      nlinarith
    simp only [matchingCount_add_one]
    split_ifs <;> omega

theorem matchingCount_tail_floor_all (n : ℕ) (a : Fin p) :
    (3 * n) / p + matchingCount n p a ≤ matchingCount (4 * n) p a ∧
    matchingCount (4 * n) p a ≤
      (3 * n) / p + matchingCount n p a + 1 := by
  obtain ⟨c, hc⟩ := (Equiv.addRight (1 : Fin p)).surjective a
  subst a
  exact matchingCount_tail_floor n c

#print axioms matchingCount_tail_floor
#print axioms matchingCount_tail_floor_all
end
end Li2Unified.Proofs.Hermite

end

section
/-! Gram change of basis for any Q-linear polynomial-valued functional.
The parameter family then supplies its own functional and original matrix. -/
open Polynomial
open scoped BigOperators
namespace Li2Unified.ParameterFamily
noncomputable section

lemma parameterU_add (lam : ℚ) (F G : ℚ[X]) :
    Li2.parameterU lam (F+G) = Li2.parameterU lam F + Li2.parameterU lam G := by
  simp only [Li2.parameterU, mul_add, derivative_add, Li2.parameterG_add]

lemma parameterU_C_mul (lam c : ℚ) (F : ℚ[X]) :
    Li2.parameterU lam (C c * F) = c * Li2.parameterU lam F := by
  unfold Li2.parameterU
  rw [show X * (C c * F) = C c * (X * F) by ring,
    derivative_C_mul, Li2.parameterG_C_mul]

lemma numeratorFunctional_add (lam : ℚ) (m : ℕ) (F G : ℚ[X]) :
    numeratorFunctional lam m (F+G) =
      numeratorFunctional lam m F + numeratorFunctional lam m G := by
  unfold numeratorFunctional
  rw [Li2.divByMonic_add (Li2.D_monic m), parameterU_add, map_add]
  simp only [eval_add, add_div, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma numeratorFunctional_C_mul (lam : ℚ) (m : ℕ) (c : ℚ) (F : ℚ[X]) :
    numeratorFunctional lam m (C c * F) = C c * numeratorFunctional lam m F := by
  unfold numeratorFunctional
  rw [Li2.divByMonic_C_mul (Li2.D_monic m), parameterU_C_mul, map_mul,
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_mul, eval_C, mul_div_assoc, map_mul]
  ring

def numeratorLinearMap (lam : ℚ) (m : ℕ) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun := numeratorFunctional lam m
  map_add' := numeratorFunctional_add lam m
  map_smul' c F := by
    simpa only [RingHom.id_apply, smul_eq_C_mul] using numeratorFunctional_C_mul lam m c F

lemma linearMap_C_mul (L : ℚ[X] →ₗ[ℚ] ℚ[X]) (c : ℚ) (F : ℚ[X]) :
    L (C c * F) = C c * L F := by
  simpa only [smul_eq_C_mul] using L.map_smul c F

def hankelFor (L : ℚ[X] →ₗ[ℚ] ℚ[X]) (h : ℕ) (R : ℚ[X]) :
    Matrix (Fin h) (Fin h) ℚ[X] :=
  fun i j => L (R * X^(i.val+j.val))

theorem gram_basis_change (L : ℚ[X] →ₗ[ℚ] ℚ[X]) (h : ℕ)
    (R : ℚ[X]) (E : Fin h → ℚ[X]) (hE : ∀ a, (E a).natDegree < h) :
    (Matrix.of fun a b => L (R * E a * E b)).det =
      C ((Li2.coeffMat E).det^2) * (hankelFor L h R).det := by
  let T := (Li2.coeffMat E).map (C : ℚ →+* ℚ[X])
  have hM : (Matrix.of fun a b => L (R * E a * E b)) =
      T * hankelFor L h R * T.transpose := by
    apply Matrix.ext
    intro a b
    have he : R * E a * E b = ∑ k : Fin h, ∑ l : Fin h,
        C (Li2.coeffMat E a k * Li2.coeffMat E b l) * (R * X^(k.val+l.val)) := by
      rw [Li2.sum_coeffMat E hE a, Li2.sum_coeffMat E hE b]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [C_mul, pow_add]
      ring
    rw [Matrix.of_apply, he, map_sum]
    simp only [map_sum, linearMap_C_mul, Matrix.mul_apply,
      Matrix.transpose_apply, T, Matrix.map_apply, hankelFor, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [C_mul]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  dsimp only [T]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_pow]
  ring

lemma hankelFor_original (lam : ℚ) (n : ℕ) :
    hankelFor (numeratorLinearMap lam (4*n)) (2*n) ((Li2.D n)^3) =
      (X:ℚ[X]) • (B lam n).map C + (A lam n).map C := by
  apply Matrix.ext
  intro i j
  simp only [hankelFor, numeratorLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, B, A, smul_eq_mul]
  rw [mul_comm ((Li2.D n)^3)]
  exact (numeratorFunctional_entry lam n (i.val+j.val)).trans (add_comm _ _)

theorem original_gram_basis_change (lam : ℚ) (n : ℕ) (E : Fin (2*n) → ℚ[X])
    (hE : ∀ a, (E a).natDegree < 2*n) :
    (Matrix.of fun a b => numeratorFunctional lam (4*n) ((Li2.D n)^3 * E a * E b)).det =
      C ((Li2.coeffMat E).det^2) * Q lam n := by
  change (Matrix.of fun a b => (numeratorLinearMap lam (4*n))
    ((Li2.D n)^3 * E a * E b)).det = _
  rw [gram_basis_change _ _ _ _ hE, hankelFor_original]
  rfl

def binomGram (lam : ℚ) (n : ℕ) : Matrix (Fin (2*n)) (Fin (2*n)) ℚ[X] :=
  Matrix.of fun a b =>
    numeratorFunctional lam (4*n) (C (Li2.Sn n) * (Li2.D n)^3 * Li2.binomPoly a * Li2.binomPoly b)

theorem Qtilde_eq_binomGram_det (lam : ℚ) (n : ℕ) : Qtilde lam n = (binomGram lam n).det := by
  have hM : binomGram lam n = C (Li2.Sn n) •
      Matrix.of fun a b : Fin (2*n) =>
        numeratorFunctional lam (4*n) ((Li2.D n)^3 * Li2.binomPoly a * Li2.binomPoly b) := by
    apply Matrix.ext
    intro a b
    simp only [binomGram, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← numeratorFunctional_C_mul]
    congr 1
    ring
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    original_gram_basis_change lam n (fun a => Li2.binomPoly a)
      (fun a => by rw [Li2.binomPoly_natDegree]; exact a.isLt),
    Li2.coeffMat_binom_det_sq, Qtilde, div_eq_mul_inv, C_mul, map_pow]
  ring

end
end Li2Unified.ParameterFamily

end


end
