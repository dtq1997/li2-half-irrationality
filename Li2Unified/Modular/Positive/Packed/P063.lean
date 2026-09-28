module
public import Li2Unified.Modular.Positive.Packed.P062
public import Li2Unified.Modular.Positive.Packed.P057
public import Li2Unified.Modular.Positive.Packed.P051
public import Li2Unified.Modular.Base.PrimeLowRationalLeading
public import Li2Unified.Modular.Base.PrimeLowScaledBlock
public import Li2Unified.Modular.Positive.Packed.P056
public import Li2Unified.Modular.Base.PrimeTopLocal
public import Li2Unified.Modular.Base.PrimeTopEntry
public import Li2Unified.Modular.Positive.Packed.P058
public import Li2Unified.Modular.Base.PrimeTopSupport

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def parameterLowRationalWeight (lam : ℚ) (a : ℕ) : ℚ :=
  lam⁻¹^a * (-(a:ℚ)) * primeLowRationalUnit a

lemma parameterLowMoment_eq_fixedLowBlock (lam : ℚ) (i j : Fin 2)
    (h : i.val+j.val < 3) :
    lowShapeVValue lam ⟨i.val+j.val,h⟩ =
      Li2Unified.ParameterFamily.fixedLowBlock lam i j := rfl

theorem parameterLow_rational_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i j : Fin (primeMultiplicity p a)) (n : ℕ) :
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    ‖(C ((p:ℚ_[p])^2) *
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
        (primeJetPoly p ⟨a,i⟩ * primeJetPoly p ⟨a,j⟩).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^(i.val+j.val) *
        ((((primeLocalUnit p a:ℚ)^2 * parameterLowRationalWeight lam a.val *
          (lowShapeVValue lam k : ℚ)) : ℚ) : ℚ_[p]))).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+1) := by
  dsimp only
  let k : ℕ := i.val+j.val
  let q : ℚ := lowShapeVValue lam
    (⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩ : Fin 3)
  let c : ℤ := primeLocalUnit p a
  let u : ℤ_[p] := primeDiscUnitConstant a.val a.isLt
  let d : ℤ_[p] := integralParameterInvPow lam hu.1 hu.2 a.val * (-(a.val:ℤ_[p])) * (c:ℤ_[p])^2
  let s : ℚ_[p] := (lam:ℚ_[p])⁻¹^a.val *
    ((p:ℚ_[p])^k * ((c*c:ℤ):ℚ_[p]) *
      (-(a.val:ℚ_[p])*((u:ℚ_[p])*(q:ℚ_[p]))))
  let t : ℚ_[p] := (p:ℚ_[p])^k *
    (((c:ℚ)^2 * parameterLowRationalWeight lam a.val * q : ℚ) : ℚ_[p])
  have hq : ‖(q:ℚ_[p])‖ ≤ 1 :=
    lowShapeVValue_norm_le_one lam hu hone hferm hp4 _
  have hfac : ‖(d:ℚ_[p])*(q:ℚ_[p])‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (PadicInt.norm_le_one d) hq (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hunit : ‖(u:ℚ_[p])-((primeLowRationalUnit a.val:ℚ):ℚ_[p])‖ ≤
      ‖(p:ℚ_[p])‖ := primeDiscUnitConstant_low_rational_norm hp4 a ha0 ha
  have hdelta : ‖(d:ℚ_[p])*(q:ℚ_[p])*
      ((u:ℚ_[p])-((primeLowRationalUnit a.val:ℚ):ℚ_[p]))‖ ≤ ‖(p:ℚ_[p])‖ := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖(p:ℚ_[p])‖ := mul_le_mul hfac hunit (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have he : s-t = (p:ℚ_[p])^k * ((d:ℚ_[p])*(q:ℚ_[p])*
      ((u:ℚ_[p])-((primeLowRationalUnit a.val:ℚ):ℚ_[p]))) := by
    dsimp only [s,t,d,parameterLowRationalWeight]
    simp only [integralParameterInvPow,integralRational,Rat.cast_inv,Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_ofNat,
      Rat.cast_natCast,Rat.cast_intCast,Int.cast_mul,PadicInt.coe_mul,
      PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast,PadicInt.coe_intCast]
    ring
  have hst : ‖s-t‖ ≤ ‖(p:ℚ_[p])‖^(k+1) := by
    rw [he,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul_of_nonneg_left hdelta (by positivity)
  apply fieldPolynomial_replace_leading_bound _ s t _ (by positivity) ?_ hst n
  intro l
  simpa only [s,k,q,c,u] using parameterLow_original_entry_leading lam hlam hu hone hferm hp4 a ha0 ha i j l

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterLow_rational_entry_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameterLow_original_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i j : Fin (primeMultiplicity p a)) :
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    GV p
      (C ((primeLocalUnit p a:ℚ)⁻¹*(primeLocalUnit p a:ℚ)⁻¹) *
        Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
          (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩).map (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-2)*parameterLowRationalWeight lam a.val *
          (lowShapeVValue lam k : ℚ)))
      (((i.val:ℚ)-1)+((j.val:ℚ)-1)+1) := by
  dsimp only
  let F : ℚ[X] := Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
    (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩).map (Int.castRingHom ℚ))
  let c : ℚ := primeLocalUnit p a
  let q : ℚ := lowShapeVValue lam
    (⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩ : Fin 3)
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p a
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw := GV_of_square_padic_leading_bound F
    (c^2*parameterLowRationalWeight lam a.val*q) (i.val+j.val)
    (parameterLow_rational_entry_leading lam hlam hunit hone hferm hp4 a ha0 ha i j)
  have hs := GV.C_mul (hi.mul hi) hraw
  have he : C (c⁻¹*c⁻¹) *
      (F-C ((p:ℚ)^(((i.val+j.val:ℕ):ℤ)-2)*(c^2*parameterLowRationalWeight lam a.val*q))) =
      C (c⁻¹*c⁻¹)*F -
        C ((p:ℚ)^(((i.val+j.val:ℕ):ℤ)-2)*parameterLowRationalWeight lam a.val*q) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  convert hs using 1 <;> push_cast <;> ring

theorem parameterLow_block_scaled_GV (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin (p-4)) (i j : Fin 2) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inl (a,i)) *
          primeBlockUnitScale hp4 (Sum.inl (a,j))) *
        parameterOriginalNumeratorEntry lam p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,j))) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-2) *
          parameterLowRationalWeight lam (a.val+1) * Li2Unified.ParameterFamily.fixedLowBlock lam i j))
      (primeBlockWeight (Sum.inl (a,i)) + primeBlockWeight (Sum.inl (a,j)) + 1) := by
  have hbI := primeBlock_original_basis_jet hp4 (Sum.inl (a,i))
    (primeLowBlockJet hp4 a i) rfl
  have hbJ := primeBlock_original_basis_jet hp4 (Sum.inl (a,j))
    (primeLowBlockJet hp4 a j) rfl
  have hsI := primeBlockUnitScale_jet hp4 (Sum.inl (a,i))
    (primeLowBlockJet hp4 a i) rfl
  have hsJ := primeBlockUnitScale_jet hp4 (Sum.inl (a,j))
    (primeLowBlockJet hp4 a j) rfl
  rw [hsI,hsJ]
  unfold parameterOriginalNumeratorEntry
  rw [hbI,hbJ]
  let A : Fin p := ⟨a.val+1,by have h := a.isLt; omega⟩
  let ii : Fin (primeMultiplicity p A) := (primeLowBlockJet hp4 a i).2
  let jj : Fin (primeMultiplicity p A) := (primeLowBlockJet hp4 a j).2
  have hA0 : 0 < A.val := by dsimp only [A]; omega
  have hA : A.val ≤ p-4 := by have h := a.isLt; dsimp only [A]; omega
  have h := parameterLow_original_scaled_GV lam hlam hunit hone hferm hp4 A hA0 hA ii jj
  simpa only [A,ii,jj,primeLowBlockJet,Fin.val_mk,primeBlockWeight,
    parameterLowMoment_eq_fixedLowBlock] using h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterLow_block_scaled_GV

end

section
open Polynomial Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def parameterTopDiscLeading (lam : ℚ) (a : Fin p) : ℚ_[p] :=
  (primeLocalUnit p a:ℚ_[p])^2 *
    (if a.val = 0 then (primeDiscUnitConstant a.val a.isLt:ℚ_[p]) * (zeroShapeUValue lam 4:ℚ_[p])
    else if a.val ≤ p-4 then 0
    else -(a.val:ℚ_[p]) * (primeDiscUnitConstant a.val a.isLt:ℚ_[p]) * (highShapeVValue lam 2:ℚ_[p]))

theorem parameterTop_zero_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*parameterTopDiscLeading lam a)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  dsimp only
  let a : Fin p := ⟨0,by omega⟩
  have hm : primeMultiplicity p a = 2 := primeMultiplicity_low hp4 a (by simp [a])
  have ht : ∃ E : ℤ[X], (primeProduct p*primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^4)*X^4*(C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E) := by
    simpa only [hm] using primeProduct_square_expansion p a
  have h := parameterDiscTest_zero_U_leading lam hu hone hferm hp4 (primeProduct p*primeProduct p) 4 ⟨4,by decide⟩
    (primeLocalUnit p a*primeLocalUnit p a) (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm)) ht n
  rw [parameterDiscContribution_cube_zero]
  simpa [parameterTopDiscLeading,a,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,
    PadicInt.coe_natCast,pow_two,mul_assoc] using h

theorem parameterTop_high_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p) (ha : p-4 < a.val) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*parameterTopDiscLeading lam a)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  have hm : primeMultiplicity p a = 1 := by unfold primeMultiplicity; rw [if_neg (by omega)]
  have ht : ∃ E : ℤ[X], (primeProduct p*primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^2)*X^2*(C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E) := by
    simpa only [hm] using primeProduct_square_expansion p a
  have h : ∀ l, ‖(C (p:ℚ_[p])*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^2*parameterTopDiscLeading lam a)).coeff l‖ ≤ ‖(p:ℚ_[p])‖^3 := by
    intro l
    rw [parameterDiscContribution_linear_high lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a ha]
    have h := parameterDiscTest_high_scaled_leading lam hu hone hferm hp4 (primeProduct p*primeProduct p) a ha
      2 ⟨2,by decide⟩ (primeLocalUnit p a*primeLocalUnit p a)
      (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm)) ht l
    have ha0 : a ≠ 0 := by
      intro he
      have hz : a.val = 0 := by simp [he]
      omega
    simpa [parameterTopDiscLeading,ha0,if_neg (by omega : a.val ≠ 0),if_neg (by omega : ¬ a.val ≤ p-4),
      PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,PadicInt.coe_natCast,pow_two,mul_assoc] using h
  have he : C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*parameterTopDiscLeading lam a) =
      C ((p:ℚ_[p])^2)*(C (p:ℚ_[p])*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) -
        C ((p:ℚ_[p])^2*parameterTopDiscLeading lam a)) := by
    simp only [C_mul,C_pow]
    ring
  rw [he]
  exact fieldPolynomial_prime_power_bound _ 2 3 h n

theorem parameterTop_low_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p) (ha0 : 0 < a.val)
    (ha : a.val ≤ p-4) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^5 := by
  have hm : primeMultiplicity p a = 2 := primeMultiplicity_low hp4 a ha
  obtain ⟨E,hE⟩ := primeProduct_square_expansion p a
  have ht : ∃ F : ℤ[X], (primeProduct p*primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^4)*F := by
    refine ⟨X^4*(C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E),?_⟩
    simpa only [hm,mul_assoc] using hE
  have h : ∀ l, ‖(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p)).coeff l‖ ≤
      ‖(p:ℚ_[p])‖^4 := by
    intro l
    rw [parameterDiscContribution_scaled_low lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a ha0 ha]
    simpa only [coeff_map,norm_pow] using parameterDiscTestScaled_factor_bound (lam^p) (parameter_power_unit lam hu) (parameterPowerRatio_integral lam hu hone hferm) hp4 _ a 4
      (parameterIntegralEta lam hu (parameterPowerRatio_integral lam hu hone hferm)) ht l
  have he : C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) =
      C ((p:ℚ_[p])^1)*(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p)) := by
    simp only [C_pow]
    ring
  rw [he]
  exact fieldPolynomial_prime_power_bound _ 1 4 h n

theorem parameterTop_disc_leading (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (a : Fin p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*parameterTopDiscLeading lam a)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  by_cases hz : a.val = 0
  · have he : a = (⟨0,by omega⟩:Fin p) := Fin.ext hz
    rw [he]
    exact parameterTop_zero_leading lam hu hone hferm hp4 n
  · by_cases hl : a.val ≤ p-4
    · simpa only [parameterTopDiscLeading,if_neg hz,if_pos hl,mul_zero,C_0,sub_zero] using
        parameterTop_low_bound lam hu hone hferm hp4 a (by omega) hl n
    · exact parameterTop_high_leading lam hu hone hferm hp4 a (by omega) n

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterTop_disc_leading

end

section
open Polynomial Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def parameterTopLeadingSum (lam : ℚ) : ℚ_[p] := ∑ a : Fin p, (lam:ℚ_[p])⁻¹^a.val*parameterTopDiscLeading lam a

theorem parameterTop_original_entry_leading (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^4*parameterTopLeadingSum (p := p) lam)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  have he : C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeProduct p).map (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p]) =
      ∑ a : Fin p, C ((lam:ℚ_[p])⁻¹^a.val)*
        (C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p)) := by
    rw [parameterNumerator_global_dissection lam hlam hu (parameterPowerRatio_integral lam hu hone hferm) hp4
      (Ne.symm (sub_ne_zero.mp (one_sub_parameter_power_unit lam hone hferm).1)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hc : (p:ℚ_[p])^4*parameterTopLeadingSum (p := p) lam =
      ∑ a : Fin p,(lam:ℚ_[p])⁻¹^a.val*((p:ℚ_[p])^4*parameterTopDiscLeading lam a) := by
    rw [parameterTopLeadingSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,hc]
  apply fieldPolynomial_sum_all_leading_bound _ _ _ (by positivity)
  intro a l
  have h := fieldPolynomial_integral_weight_leading
    (C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu (parameterPowerRatio_integral lam hu hone hferm) hp4 a (primeProduct p*primeProduct p))
    (integralParameterInvPow lam hu.1 hu.2 a.val) _ _ (parameterTop_disc_leading lam hu hone hferm hp4 a) l
  simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterTop_original_entry_leading

end

section
open Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameterTopLeadingSum_four (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0) (hp4 : 3 < p) :
    parameterTopLeadingSum (p := p) lam =
      parameterTopDiscLeading (p := p) lam ⟨0,by omega⟩ +
      (lam:ℚ_[p])⁻¹^(p-1)*parameterTopDiscLeading (p := p) lam ⟨p-1,by omega⟩ +
      (lam:ℚ_[p])⁻¹^(p-2)*parameterTopDiscLeading (p := p) lam ⟨p-2,by omega⟩ +
      (lam:ℚ_[p])⁻¹^(p-3)*parameterTopDiscLeading (p := p) lam ⟨p-3,by omega⟩ := by
  classical
  let a0 : Fin p := ⟨0,by omega⟩
  let a1 : Fin p := ⟨p-1,by omega⟩
  let a2 : Fin p := ⟨p-2,by omega⟩
  let a3 : Fin p := ⟨p-3,by omega⟩
  let s : Finset (Fin p) := {a0,a1,a2,a3}
  let F : Fin p → ℚ_[p] := fun a => (lam:ℚ_[p])⁻¹^a.val*parameterTopDiscLeading lam a
  have he : (∑ a : Fin p,F a) = ∑ a ∈ s,F a := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro a _ ha
    have hn : ¬ (a.val=0 ∨ a.val=p-1 ∨ a.val=p-2 ∨ a.val=p-3) := by
      simpa only [s,a0,a1,a2,a3,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] using ha
    have hz : a.val ≠ 0 := by omega
    have hl : a.val ≤ p-4 := by have := a.isLt; omega
    simp only [F,parameterTopDiscLeading,if_neg hz,if_pos hl,mul_zero]
  have h01 : a0 ≠ a1 := by apply Fin.ne_of_val_ne; dsimp [a0,a1]; omega
  have h02 : a0 ≠ a2 := by apply Fin.ne_of_val_ne; dsimp [a0,a2]; omega
  have h03 : a0 ≠ a3 := by apply Fin.ne_of_val_ne; dsimp [a0,a3]; omega
  have h12 : a1 ≠ a2 := by apply Fin.ne_of_val_ne; dsimp [a1,a2]; omega
  have h13 : a1 ≠ a3 := by apply Fin.ne_of_val_ne; dsimp [a1,a3]; omega
  have h23 : a2 ≠ a3 := by apply Fin.ne_of_val_ne; dsimp [a2,a3]; omega
  change (∑ a : Fin p,F a) = _
  rw [he]
  dsimp only [s]
  rw [Finset.sum_insert (by simp [h01,h02,h03]),
    Finset.sum_insert (by simp [h12,h13]),
    Finset.sum_insert (by simp [h23]),Finset.sum_singleton]
  simp only [F,a0,a1,a2,a3,Fin.val_mk,pow_zero,one_mul]
  ring

theorem parameterTopLeadingSum_weighted (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0) (hp4 : 3 < p) :
    parameterTopLeadingSum (p := p) lam =
      (primeLocalUnit p ⟨0,by omega⟩:ℚ_[p])^2*
        (primeDiscUnitConstant (p := p) 0 (by omega):ℚ_[p])*(zeroShapeUValue lam 4:ℚ_[p]) +
      ((parameterHighDiscWeight (p := p) lam hu ⟨p-1,by omega⟩:ℚ_[p])*(primeLocalUnit p ⟨p-1,by omega⟩:ℚ_[p])^2 +
       (parameterHighDiscWeight (p := p) lam hu ⟨p-2,by omega⟩:ℚ_[p])*(primeLocalUnit p ⟨p-2,by omega⟩:ℚ_[p])^2 +
       (parameterHighDiscWeight (p := p) lam hu ⟨p-3,by omega⟩:ℚ_[p])*(primeLocalUnit p ⟨p-3,by omega⟩:ℚ_[p])^2)*(highShapeVValue lam 2:ℚ_[p]) := by
  rw [parameterTopLeadingSum_four lam hu hp4]
  simp only [parameterTopDiscLeading,Fin.val_mk,ite_true,
    if_neg (by omega : p-1 ≠ 0),if_neg (by omega : p-2 ≠ 0),if_neg (by omega : p-3 ≠ 0),
    if_neg (by omega : ¬ p-1 ≤ p-4),if_neg (by omega : ¬ p-2 ≤ p-4),if_neg (by omega : ¬ p-3 ≤ p-4),
    parameterHighDiscWeight,integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast,
    Rat.cast_div,Rat.cast_neg,Rat.cast_ofNat]
  ring


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterTopLeadingSum_weighted

end


end
