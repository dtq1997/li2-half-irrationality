module
public import Li2Unified.Modular.Base.PrimeReferenceMatrix
public import Li2Unified.Modular.Base.PrimeLowWeightUnit
public import Mathlib.LinearAlgebra.Matrix.Block

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def primeReferenceLowCore (p : ℕ) :
    Matrix (Fin (p-4) × Fin 2) (Fin (p-4) × Fin 2) ℚ :=
  (Matrix.blockDiagonal (fun a : Fin (p-4) =>
    primeLowRationalWeight (a.val+1) • lowBlock)).submatrix
      (Equiv.prodComm (Fin (p-4)) (Fin 2))
      (Equiv.prodComm (Fin (p-4)) (Fin 2))

lemma primeReferenceLowCore_apply (a b : Fin (p-4)) (i j : Fin 2) :
    primeReferenceLowCore p (a,i) (b,j) =
      if a = b then primeLowRationalWeight (a.val+1)*lowBlock i j else 0 := rfl

def primeReferenceCore (p : ℕ) :
    Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ :=
  Matrix.fromBlocks (primeReferenceLowCore p) 0 0 edgeBlock

def primeReferenceMainConstant (p : ℕ) : ℚ :=
  (∏ a : Fin (p-4), (primeLowRationalWeight (a.val+1))^2) *
    (851/6:ℚ)^(p-4) * 27740

lemma primeReferenceLowCore_det :
    (primeReferenceLowCore p).det =
      (∏ a : Fin (p-4), (primeLowRationalWeight (a.val+1))^2) *
        (851/6:ℚ)^(p-4) := by
  classical
  unfold primeReferenceLowCore
  rw [Matrix.det_submatrix_equiv_self,Matrix.det_blockDiagonal]
  simp_rw [Matrix.det_smul,Fintype.card_fin,lowBlock_det]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma primeReferenceCore_det :
    (primeReferenceCore p).det = primeReferenceMainConstant p := by
  unfold primeReferenceCore primeReferenceMainConstant
  rw [Matrix.det_fromBlocks_zero₂₁,primeReferenceLowCore_det,edgeBlock_det]

/-- Integer row powers; the edge half-power is placed in the column factor. -/
def primeReferenceRowExponent : PrimeBlockIndex p → ℤ
  | Sum.inl ai => (ai.2.val:ℤ)-1
  | Sum.inr k => primeEdgeIntegerWeight k

def primeReferenceColExponent : PrimeBlockIndex p → ℤ
  | Sum.inl ai => (ai.2.val:ℤ)-1
  | Sum.inr k => primeEdgeIntegerWeight k+1

lemma primeReferenceMatrix_factor_entry (x y : PrimeBlockIndex p) :
    primeReferenceMatrix p x y =
      C ((p:ℚ)^primeReferenceRowExponent x *
        ((p:ℚ)^primeReferenceColExponent y * primeReferenceCore p x y)) := by
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rcases x with ⟨a,i⟩ | k <;> rcases y with ⟨b,j⟩ | l
  · by_cases hab : a = b
    · subst b
      simp only [primeReferenceMatrix,primeReferenceCore,Matrix.fromBlocks_apply₁₁,
        primeReferenceLowCore_apply,if_pos rfl,ite_true,
        primeReferenceRowExponent,primeReferenceColExponent]
      congr 1
      rw [← mul_assoc ((p:ℚ)^((i.val:ℤ)-1)) ((p:ℚ)^((j.val:ℤ)-1))
        (primeLowRationalWeight (a.val+1)*lowBlock i j),← zpow_add₀ hpq]
      rw [show ((i.val:ℤ)-1)+((j.val:ℤ)-1) = (i.val:ℤ)+(j.val:ℤ)-2 by ring]
      ring
    · simp only [primeReferenceMatrix,primeReferenceCore,Matrix.fromBlocks_apply₁₁,
        primeReferenceLowCore_apply,if_neg hab,mul_zero,C_0]
  · simp only [primeReferenceMatrix,primeReferenceCore,Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply,mul_zero,C_0]
  · simp only [primeReferenceMatrix,primeReferenceCore,Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply,mul_zero,C_0]
  · simp only [primeReferenceMatrix,primeReferenceCore,Matrix.fromBlocks_apply₂₂,
      primeReferenceRowExponent,primeReferenceColExponent]
    congr 1
    rw [← mul_assoc ((p:ℚ)^primeEdgeIntegerWeight k)
      ((p:ℚ)^(primeEdgeIntegerWeight l+1)) (edgeBlock k l),← zpow_add₀ hpq]
    rw [show primeEdgeIntegerWeight k+(primeEdgeIntegerWeight l+1) =
      primeEdgeIntegerWeight k+primeEdgeIntegerWeight l+1 by ring]

lemma primeReference_exponent_sum (hp4 : 3 < p) :
    (∑ x : PrimeBlockIndex p, primeReferenceRowExponent x) +
      (∑ x : PrimeBlockIndex p, primeReferenceColExponent x) =
      -2*((p-1:ℕ):ℤ) := by
  have hlow :
      (∑ ai : Fin (p-4) × Fin 2,
        (primeReferenceRowExponent (Sum.inl ai)+primeReferenceColExponent (Sum.inl ai))) =
        -2*((p-4:ℕ):ℤ) := by
    rw [Fintype.sum_prod_type]
    simp [primeReferenceRowExponent,primeReferenceColExponent,Fin.sum_univ_two] <;> ring
  have hedge :
      (∑ k : Fin 6, (primeReferenceRowExponent (p := p) (Sum.inr k) +
        primeReferenceColExponent (p := p) (Sum.inr k))) = -6 := by
    norm_num [primeReferenceRowExponent,primeReferenceColExponent,
      primeEdgeIntegerWeight,Fin.sum_univ_succ]
  rw [← Finset.sum_add_distrib,Fintype.sum_sum_type,hlow,hedge]
  have h4 : ((p-4:ℕ):ℤ) = (p:ℤ)-4 := Nat.cast_sub (by omega)
  have h1 : ((p-1:ℕ):ℤ) = (p:ℤ)-1 := Nat.cast_sub (by omega)
  rw [h4,h1]
  ring

lemma primeReference_prod_zpow {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (e : ι → ℤ) :
    (∏ x ∈ S, (p:ℚ)^(e x)) = (p:ℚ)^(∑ x ∈ S, e x) := by
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,zpow_add₀ hpq]

theorem primeReferenceMatrix_det (hp4 : 3 < p) :
    (primeReferenceMatrix p).det =
      C ((p:ℚ)^(-2*((p-1:ℕ):ℤ))*primeReferenceMainConstant p) := by
  classical
  let A : Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ := Matrix.of (fun x y =>
    (p:ℚ)^primeReferenceRowExponent x *
      ((p:ℚ)^primeReferenceColExponent y * primeReferenceCore p x y))
  have hN : primeReferenceMatrix p = (Polynomial.C : ℚ →+* ℚ[X]).mapMatrix A := by
    funext x y
    exact primeReferenceMatrix_factor_entry x y
  have hA : A.det =
      ((∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceColExponent x)) *
          (primeReferenceCore p).det := by
    dsimp only [A]
    rw [Matrix.det_mul_column]
    change
      (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (Matrix.of (fun x y : PrimeBlockIndex p =>
          (p:ℚ)^primeReferenceColExponent y * primeReferenceCore p x y)).det =
      ((∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceColExponent x)) *
          (primeReferenceCore p).det
    rw [Matrix.det_mul_row]
    ring
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hr := primeReference_prod_zpow (p := p) Finset.univ
    (primeReferenceRowExponent (p := p))
  have hc := primeReference_prod_zpow (p := p) Finset.univ
    (primeReferenceColExponent (p := p))
  have hscale :
      (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceRowExponent x) *
        (∏ x : PrimeBlockIndex p, (p:ℚ)^primeReferenceColExponent x) =
        (p:ℚ)^(-2*((p-1:ℕ):ℤ)) := by
    rw [hr,hc,← zpow_add₀ hpq,primeReference_exponent_sum hp4]
  calc
    (primeReferenceMatrix p).det = C A.det := by
      rw [hN,← (Polynomial.C : ℚ →+* ℚ[X]).map_det A]
    _ = C ((p:ℚ)^(-2*((p-1:ℕ):ℤ))*primeReferenceMainConstant p) := by
      rw [hA,hscale,primeReferenceCore_det]

theorem primeReferenceMainConstant_unit (hp73 : 73 < p) :
    primeReferenceMainConstant p ≠ 0 ∧
      padicValRat p (primeReferenceMainConstant p) = 0 := by
  have hp4 : 3 < p := by omega
  have hnat (k : ℕ) (hk0 : 0 < k) (hkp : k < p) :
      (k:ℚ) ≠ 0 ∧ padicValRat p (k:ℚ) = 0 := by
    refine ⟨by exact_mod_cast hk0.ne', ?_⟩
    rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt hk0 hkp)]
    rfl
  have hmul (x y : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0)
      (hy : y ≠ 0 ∧ padicValRat p y = 0) :
      x*y ≠ 0 ∧ padicValRat p (x*y) = 0 :=
    ⟨mul_ne_zero hx.1 hy.1,by rw [padicValRat.mul hx.1 hy.1,hx.2,hy.2,add_zero]⟩
  have hpow (x : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0) (n : ℕ) :
      x^n ≠ 0 ∧ padicValRat p (x^n) = 0 :=
    ⟨pow_ne_zero n hx.1,by rw [padicValRat.pow hx.1,hx.2,mul_zero]⟩
  have hdiv (x y : ℚ) (hx : x ≠ 0 ∧ padicValRat p x = 0)
      (hy : y ≠ 0 ∧ padicValRat p y = 0) :
      x/y ≠ 0 ∧ padicValRat p (x/y) = 0 :=
    ⟨div_ne_zero hx.1 hy.1,by rw [padicValRat.div hx.1 hy.1,hx.2,hy.2,sub_self]⟩
  have h851 : (851:ℚ) = 23*37 := by exact_mod_cast exceptional_factors.1
  have h27740 : (27740:ℚ) = 4*5*19*73 := by exact_mod_cast exceptional_factors.2
  have hn851 : (851:ℚ) ≠ 0 ∧ padicValRat p (851:ℚ) = 0 := by
    rw [h851]
    exact hmul _ _ (hnat 23 (by norm_num) (by omega))
      (hnat 37 (by norm_num) (by omega))
  have hlow : (851/6:ℚ) ≠ 0 ∧ padicValRat p (851/6:ℚ) = 0 :=
    hdiv _ _ hn851 (hnat 6 (by norm_num) (by omega))
  have hedge : (27740:ℚ) ≠ 0 ∧ padicValRat p (27740:ℚ) = 0 := by
    rw [h27740]
    exact hmul _ _
      (hmul _ _ (hmul _ _
        (hnat 4 (by norm_num) (by omega)) (hnat 5 (by norm_num) (by omega)))
        (hnat 19 (by norm_num) (by omega)))
      (hnat 73 (by norm_num) (by omega))
  have hprod := rational_prime_unit_finset_prod (p := p) Finset.univ
    (fun a : Fin (p-4) => (primeLowRationalWeight (a.val+1))^2) (by
      intro a _
      have ha := a.isLt
      exact hpow _ (primeLowRationalWeight_unit (p := p) hp4 (a.val+1)
        (by omega) (by omega)) 2)
  unfold primeReferenceMainConstant
  exact hmul _ _ (hmul _ _ hprod (hpow _ hlow (p-4))) hedge

end
end Li2

end
