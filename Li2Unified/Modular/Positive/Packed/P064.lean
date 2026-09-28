module
public import Li2Unified.Modular.Positive.Packed.P063
public import Li2Unified.Modular.Positive.Packed.P061

set_option backward.privateInPublic true

@[expose] public section

section
open Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

private lemma near_norm (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1)
    (hxy : ‖x-y‖ ≤ ‖(p:ℚ_[p])‖) : ‖y‖ ≤ 1 := by
  rw [show y = x-(x-y) by ring,sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  rw [norm_neg]
  exact max_le hx (hxy.trans (PadicInt.norm_le_one (p:ℤ_[p])))

private lemma near_add {x x' y y' : ℚ_[p]}
    (hx : ‖x-x'‖ ≤ ‖(p:ℚ_[p])‖) (hy : ‖y-y'‖ ≤ ‖(p:ℚ_[p])‖) :
    ‖(x+y)-(x'+y')‖ ≤ ‖(p:ℚ_[p])‖ := by
  rw [show (x+y)-(x'+y') = (x-x')+(y-y') by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private lemma near_mul {x x' y y' : ℚ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hxx : ‖x-x'‖ ≤ ‖(p:ℚ_[p])‖) (hyy : ‖y-y'‖ ≤ ‖(p:ℚ_[p])‖) :
    ‖x*y-x'*y'‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hx' : ‖x'‖ ≤ 1 := near_norm x x' hx hxx
  rw [show x*y-x'*y' = (x-x')*y+x'*(y-y') by ring]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · rw [norm_mul]
    simpa using mul_le_mul hxx hy (norm_nonneg _) (norm_nonneg _)
  · rw [norm_mul]
    simpa using mul_le_mul hx' hyy (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

private lemma near_sq {x x' : ℚ_[p]} (hx : ‖x‖ ≤ 1)
    (hxx : ‖x-x'‖ ≤ ‖(p:ℚ_[p])‖) : ‖x^2-x'^2‖ ≤ ‖(p:ℚ_[p])‖ := by
  simpa only [pow_two] using near_mul hx hx hxx hxx

private def zeroCoefficient (hp4 : 3 < p) : ℤ_[p] :=
  (primeLocalUnit p ⟨0,by omega⟩:ℤ_[p])^2 * primeDiscUnitConstant 0 (by omega)

private def highCoefficient (lam : ℚ) (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hp4 : 3 < p) (ell : Fin 3) : ℤ_[p] :=
  parameterHighDiscWeight lam hu (primeHighBlockJet hp4 ell).1 *
    (primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℤ_[p])^2

private lemma zeroCoefficient_norm (hp4 : 3 < p) :
    ‖(zeroCoefficient hp4:ℚ_[p])-(1/6:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
  have hc : ‖(primeLocalUnit p ⟨0,by omega⟩:ℚ_[p])‖ ≤ 1 :=
    PadicInt.norm_le_one (primeLocalUnit p ⟨0,by omega⟩:ℤ_[p])
  have hc2 : ‖(primeLocalUnit p ⟨0,by omega⟩:ℚ_[p])^2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hc
  have h := near_mul hc2 (PadicInt.norm_le_one (primeDiscUnitConstant (p := p) 0 (by omega)))
    (near_sq hc (primeLocalUnit_zero_norm hp4)) (primeDiscUnitConstant_zero_norm hp4)
  norm_num [show ((6:ℤ_[p]):ℚ_[p]) = 6 from rfl] at h
  simpa [zeroCoefficient] using h

private lemma highCoefficient_norm (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (ell : Fin 3) :
    ‖(highCoefficient lam hu hp4 ell:ℚ_[p])-
      ((parameterHighRationalWeight lam ell * (primeHighRationalLocalUnit ell)^2:ℚ):ℚ_[p])‖ ≤
      ‖(p:ℚ_[p])‖ := by
  have hc : ‖(primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ_[p])‖ ≤ 1 :=
    PadicInt.norm_le_one (primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℤ_[p])
  have hc2 : ‖(primeLocalUnit p (primeHighBlockJet hp4 ell).1:ℚ_[p])^2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hc
  have h := near_mul (PadicInt.norm_le_one
      (parameterHighDiscWeight lam hu (primeHighBlockJet hp4 ell).1)) hc2
    (parameterHighRationalWeight_norm lam hu hferm hp4 ell)
    (near_sq hc (primeHighRationalLocalUnit_norm hp4 ell))
  simpa only [highCoefficient,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,
    Rat.cast_mul,Rat.cast_pow] using h

theorem parameterTopLeadingSum_norm (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) :
    ‖parameterTopLeadingSum (p := p) lam-(fixedCornerBlock lam 5 5:ℚ_[p])‖ ≤
      ‖(p:ℚ_[p])‖ := by
  let z : ℤ_[p] := zeroCoefficient hp4
  let w : ℤ_[p] := highCoefficient lam hu hp4 0 +
    highCoefficient lam hu hp4 1 + highCoefficient lam hu hp4 2
  let Z : ℚ_[p] := (zeroShapeUValue lam 4:ℚ_[p])
  let H : ℚ_[p] := (highShapeVValue lam 2:ℚ_[p])
  have hz : ‖(z:ℚ_[p])-(1/6:ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := zeroCoefficient_norm hp4
  have hw : ‖(w:ℚ_[p])-((-1/2+lam/2-lam^2/6:ℚ):ℚ_[p])‖ ≤ ‖(p:ℚ_[p])‖ := by
    have h := near_add (near_add (highCoefficient_norm lam hu hferm hp4 0)
      (highCoefficient_norm lam hu hferm hp4 1)) (highCoefficient_norm lam hu hferm hp4 2)
    have he : parameterHighRationalWeight lam 0 * (primeHighRationalLocalUnit 0)^2 +
        parameterHighRationalWeight lam 1 * (primeHighRationalLocalUnit 1)^2 +
        parameterHighRationalWeight lam 2 * (primeHighRationalLocalUnit 2)^2 =
        -1/2+lam/2-lam^2/6 := by
      change (-2:ℚ)*(1/2)^2+(lam/2)*(-1)^2+(-2*lam^2/3)*(1/2)^2 = _
      ring
    rw [← he]
    simpa only [w,PadicInt.coe_add,Rat.cast_add] using h
  have hZ : ‖Z‖ ≤ 1 := zeroShapeUValue_norm_le_one lam hu hone hferm hp4 4
  have hH : ‖H‖ ≤ 1 := highShapeVValue_norm_le_one lam hu hone hferm hp4 2
  have hzZ := near_mul (PadicInt.norm_le_one z) hZ hz (by simp : ‖Z-Z‖ ≤ ‖(p:ℚ_[p])‖)
  have hwH := near_mul (PadicInt.norm_le_one w) hH hw (by simp : ‖H-H‖ ≤ ‖(p:ℚ_[p])‖)
  have h := near_add hzZ hwH
  have he : parameterTopLeadingSum (p := p) lam = (z:ℚ_[p])*Z+(w:ℚ_[p])*H := by
    rw [parameterTopLeadingSum_weighted lam hu hp4]
    dsimp only [z,w,Z,H,zeroCoefficient,highCoefficient,primeHighBlockJet]
    simp only [Fin.val_mk,PadicInt.coe_add,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast]
    norm_num
  rw [he]
  have hf : (fixedCornerBlock lam 5 5:ℚ_[p]) =
      (1/6:ℚ_[p])*Z+((-1/2+lam/2-lam^2/6:ℚ):ℚ_[p])*H := by
    change (((-1/2+lam/2-lam^2/6)*fixedHighMoment lam 2+fixedZeroMoment lam 4/6:ℚ):ℚ_[p]) = _
    have hZ' : (fixedZeroMoment lam 4:ℚ_[p]) = Z := rfl
    have hH' : (fixedHighMoment lam 2:ℚ_[p]) = H := rfl
    simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,hZ',hH']
    ring
  rw [hf]
  exact h

end
end Li2Unified.Proofs.PrimeEdge

#print axioms Li2Unified.Proofs.PrimeEdge.parameterTopLeadingSum_norm

end


end
