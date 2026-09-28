module
public import Li2Unified.Modular.Positive.Packed.P051
public import Li2Unified.Modular.Base.PrimeReferenceDeterminant

set_option backward.privateInPublic true

@[expose] public section

section
/-! Parameter-dependent reference blocks, independent of the actual matrix.
The entrywise comparison with the original functional remains a separate task. -/
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
open Li2Unified.ParameterFamily

def parameterLowWeight (lam : ℚ) (a : ℕ) : ℚ :=
  lam⁻¹^a * (-(a:ℚ)) * Li2.primeLowRationalUnit a

def parameterLowCore (lam : ℚ) (p : ℕ) :
    Matrix (Fin (p-4) × Fin 2) (Fin (p-4) × Fin 2) ℚ :=
  (Matrix.blockDiagonal (fun a : Fin (p-4) =>
    parameterLowWeight lam (a.val+1) • fixedLowBlock lam)).submatrix
      (Equiv.prodComm (Fin (p-4)) (Fin 2))
      (Equiv.prodComm (Fin (p-4)) (Fin 2))

def parameterReferenceCore (lam : ℚ) (p : ℕ) (corner : Matrix (Fin 6) (Fin 6) ℚ) :
    Matrix (Li2.PrimeBlockIndex p) (Li2.PrimeBlockIndex p) ℚ :=
  Matrix.fromBlocks (parameterLowCore lam p) 0 0 corner

theorem parameterLowCore_apply (lam : ℚ) (p : ℕ)
    (a b : Fin (p-4)) (i j : Fin 2) :
    parameterLowCore lam p (a,i) (b,j) =
      if a = b then parameterLowWeight lam (a.val+1)*fixedLowBlock lam i j else 0 := rfl

theorem parameterLowCore_det (lam : ℚ) (p : ℕ) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (parameterLowCore lam p).det =
      (∏ a : Fin (p-4), (parameterLowWeight lam (a.val+1))^2) *
        (lowBlockConstant lam)^(p-4) := by
  classical
  unfold parameterLowCore
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  simp_rw [Matrix.det_smul, Fintype.card_fin, fixedLowBlock_det lam h0 h1]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem parameterReferenceCore_det (lam : ℚ) (p : ℕ)
    (corner : Matrix (Fin 6) (Fin 6) ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1) :
    (parameterReferenceCore lam p corner).det =
      (∏ a : Fin (p-4), (parameterLowWeight lam (a.val+1))^2) *
        (lowBlockConstant lam)^(p-4) * corner.det := by
  unfold parameterReferenceCore
  rw [Matrix.det_fromBlocks_zero₂₁, parameterLowCore_det lam p h0 h1]

theorem parameterLowWeight_unit (lam : ℚ) {p : ℕ} [Fact p.Prime]
    (hp4 : 3 < p) (hunit : lam ≠ 0 ∧ padicValRat p lam = 0)
    (a : ℕ) (ha0 : 0 < a) (ha : a ≤ p-4) :
    parameterLowWeight lam a ≠ 0 ∧ padicValRat p (parameterLowWeight lam a) = 0 := by
  have hm2 : (-2:ℚ) ≠ 0 := by norm_num
  have hu0 : lam⁻¹ / (-2:ℚ) ≠ 0 := div_ne_zero (inv_ne_zero hunit.1) hm2
  have huval : padicValRat p (lam⁻¹ / (-2:ℚ)) = 0 := by
    rw [padicValRat.div (inv_ne_zero hunit.1) hm2, padicValRat.inv,
      hunit.2, padicValRat.neg, Li2.two_valuation_zero (by omega)]
    norm_num
  have he : parameterLowWeight lam a =
      (lam⁻¹ / (-2:ℚ))^a * Li2.primeLowRationalWeight a := by
    unfold parameterLowWeight Li2.primeLowRationalWeight
    rw [div_pow]
    field_simp
  have hw := Li2.primeLowRationalWeight_unit hp4 a ha0 ha
  rw [he]
  refine ⟨mul_ne_zero (pow_ne_zero _ hu0) hw.1, ?_⟩
  rw [padicValRat.mul (pow_ne_zero _ hu0) hw.1,
    padicValRat.pow, huval, hw.2]
  simp

#print axioms parameterReferenceCore_det
#print axioms parameterLowWeight_unit

end
end Li2Unified.Proofs.PrimeEdge

end


end
