module
public import Li2Unified.Modular.Positive.Packed.P056
public import Li2Unified.Modular.Positive.Packed.P058
public import Li2Unified.Modular.Base.PrimeHighRationalLeading

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Actual high/high and high/G entries; the full top/top sum is excluded. -/
theorem parameterHigh_rational_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3)
    (i j : Fin 2) (hij : i.val+j.val < 2) (n : ℕ) :
    let k : Fin 3 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    ‖(C (p:ℚ_[p]) *
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell i*primeHighBlockPoly hp4 ell j).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^(i.val+j.val) *
        ((c^2*parameterHighRationalWeight lam ell*(highShapeVValue lam k : ℚ) : ℚ):ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let a : Fin p := (primeHighBlockJet hp4 ell).1
  let k : ℕ := i.val+j.val
  let q : ℚ := highShapeVValue lam (⟨i.val+j.val,by omega⟩ : Fin 3)
  let c : ℤ := primeLocalUnit p a
  let u : ℤ_[p] := primeDiscUnitConstant a.val a.isLt
  let d : ℤ_[p] := (c:ℤ_[p])^2
  let e : ℤ_[p] := (p:ℤ_[p])^k * ((c*c:ℤ):ℤ_[p])
  let s : ℚ_[p] := (lam:ℚ_[p])⁻¹^a.val *
    ((e:ℚ_[p]) * (-(a.val:ℚ_[p])*((u:ℚ_[p])*(q:ℚ_[p]))))
  let t : ℚ_[p] := (p:ℚ_[p])^k *
    (((c:ℚ)^2*parameterHighRationalWeight lam ell*q : ℚ):ℚ_[p])
  have hq : ‖(q:ℚ_[p])‖ ≤ 1 := highShapeVValue_norm_le_one lam hu hone hferm hp4 _
  have hfac : ‖(d:ℚ_[p])*(q:ℚ_[p])‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (PadicInt.norm_le_one d) hq (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hunit : ‖(parameterHighDiscWeight lam hu a:ℚ_[p])-
      ((parameterHighRationalWeight lam ell:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ :=
    parameterHighRationalWeight_norm lam hu hferm hp4 ell
  have hdelta : ‖(d:ℚ_[p])*(q:ℚ_[p]) *
      ((parameterHighDiscWeight lam hu a:ℚ_[p])-((parameterHighRationalWeight lam ell:ℚ):ℚ_[p]))‖ ≤
      ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℚ_[p])‖ := mul_le_mul hfac hunit (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have he : s-t = (p:ℚ_[p])^k * ((d:ℚ_[p])*(q:ℚ_[p]) *
      ((parameterHighDiscWeight lam hu a:ℚ_[p])-((parameterHighRationalWeight lam ell:ℚ):ℚ_[p]))) := by
    dsimp only [s,t,d,e,u,parameterHighDiscWeight]
    simp only [integralParameterInvPow,integralRational,Rat.cast_inv,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast,
      PadicInt.coe_intCast,PadicInt.coe_neg,Int.cast_mul,Rat.cast_mul,
      Rat.cast_pow,Rat.cast_intCast]
    ring
  have hst : ‖s-t‖ ≤ ‖(p:ℚ_[p])‖^(k+1) := by
    rw [he,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  apply fieldPolynomial_replace_leading_bound _ s t _ (by positivity) ?_ hst n
  intro l
  simpa only [primeHighBlockPoly,primeHighAugmentedIndex,Fin.val_mk,s,e,k,q,c,u,a]
    using parameterHigh_original_entry_leading lam hlam hu hone hferm hp4 (primeHighBlockJet hp4 ell).1
      (primeHighBlock_above hp4 ell)
      (primeHighAugmentedIndex hp4 ell i) (primeHighAugmentedIndex hp4 ell j)
      (by simpa only [primeHighAugmentedIndex,Fin.val_mk] using hij) l

theorem parameterHigh_rational_entry_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3)
    (i j : Fin 2) (hij : i.val+j.val < 2) :
    let k : Fin 3 := ⟨i.val+j.val,by omega⟩
    let c : ℚ := primeLocalUnit p (primeHighBlockJet hp4 ell).1
    GV p
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeHighBlockPoly hp4 ell i*primeHighBlockPoly hp4 ell j).map
          (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-1) *
          (c^2*parameterHighRationalWeight lam ell*(highShapeVValue lam k : ℚ))))
      ((i.val:ℚ)+(j.val:ℚ)) := by
  dsimp only
  have h := GV_of_linear_padic_leading_bound
    (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
      (primeHighBlockPoly hp4 ell i*primeHighBlockPoly hp4 ell j).map
        (Int.castRingHom ℚ)))
    ((primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ)^2 *
      parameterHighRationalWeight lam ell *
      (highShapeVValue lam (⟨i.val+j.val,by omega⟩ : Fin 3) : ℚ)) (i.val+j.val)
    (parameterHigh_rational_entry_leading lam hlam hu hone hferm hp4 ell i j hij)
  convert h using 1 <;> push_cast <;> ring


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterHigh_rational_entry_GV

end


end
