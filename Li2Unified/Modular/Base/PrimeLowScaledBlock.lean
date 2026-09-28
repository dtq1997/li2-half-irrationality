module
public import Li2Unified.Modular.Base.PrimeLowRationalLeading
public import Li2Unified.Modular.Base.PrimeCrossValuation
public import Li2Unified.Modular.Base.PrimeBlockIndex

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem GV_of_square_padic_leading_bound (F : ℚ[X]) (r : ℚ) (k : ℕ)
    (h : ∀ n, ‖(C ((p:ℚ_[p])^2)*F.map (Rat.castHom ℚ_[p]) -
      C ((p:ℚ_[p])^k*(r:ℚ_[p]))).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(k+1)) :
    GV p (F-C ((p:ℚ)^((k:ℤ)-2)*r)) ((k:ℚ)-1) := by
  let E : ℚ[X] := C ((p:ℚ)^2)*F-C ((p:ℚ)^k*r)
  have hmap : E.map (Rat.castHom ℚ_[p]) =
      C ((p:ℚ_[p])^2)*F.map (Rat.castHom ℚ_[p]) -
        C ((p:ℚ_[p])^k*(r:ℚ_[p])) := by
    simp only [E,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
      Rat.coe_castHom,Rat.cast_pow,Rat.cast_natCast,Rat.cast_mul]
  have hE : GV p E ((k+1 : ℕ) : ℚ) := by
    intro n
    apply VG_of_padic_norm_pow_le _ (k+1)
    have hn := h n
    rw [← hmap] at hn
    simpa only [coeff_map,Rat.coe_castHom] using hn
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp2 : (p:ℚ)^(-2:ℤ)*(p:ℚ)^2 = 1 := by
    simp only [zpow_neg,zpow_ofNat]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hpq)
  have hpk : (p:ℚ)^(-2:ℤ)*(p:ℚ)^k = (p:ℚ)^((k:ℤ)-2) := by
    rw [zpow_sub₀ hpq]
    simp only [zpow_neg,zpow_ofNat,zpow_natCast,div_eq_mul_inv]
    ring
  have he : C ((p:ℚ)^(-2:ℤ))*E = F-C ((p:ℚ)^((k:ℤ)-2)*r) := by
    dsimp only [E]
    rw [mul_sub,← mul_assoc,← C_mul,hp2,C_1,one_mul,← C_mul]
    rw [← mul_assoc,hpk]
  have hh := GV.C_mul (VG.primePow (p := p) (-2)) hE
  rw [he] at hh
  exact hh.mono (by push_cast <;> linarith)

/-- Both inverse factors are proved valuation-zero units. -/
theorem primeLow_original_scaled_GV (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i j : Fin (primeMultiplicity p a)) :
    let k : Fin 3 := ⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩
    GV p
      (C ((primeLocalUnit p a:ℚ)⁻¹*(primeLocalUnit p a:ℚ)⁻¹) *
        numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
          (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩).map (Int.castRingHom ℚ)) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-2)*primeLowRationalWeight a.val *
          (![95/4,-253/4,2093/12] k : ℚ)))
      (((i.val:ℚ)-1)+((j.val:ℚ)-1)+1) := by
  dsimp only
  let F : ℚ[X] := numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
    (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨a,j⟩).map (Int.castRingHom ℚ))
  let c : ℚ := primeLocalUnit p a
  let q : ℚ := ![95/4,-253/4,2093/12]
    (⟨i.val+j.val,primeLow_pair_lt_three hp4 a ha i j⟩ : Fin 3)
  have hu : c ≠ 0 ∧ padicValRat p c = 0 := primeLocalUnit_unit p a
  have hi : VG p c⁻¹ 0 := rational_unit_inverse_VG c hu.1 hu.2
  have hraw := GV_of_square_padic_leading_bound F
    (c^2*primeLowRationalWeight a.val*q) (i.val+j.val)
    (primeLow_rational_entry_leading hp4 a ha0 ha i j)
  have hs := GV.C_mul (hi.mul hi) hraw
  have he : C (c⁻¹*c⁻¹) *
      (F-C ((p:ℚ)^(((i.val+j.val:ℕ):ℤ)-2)*(c^2*primeLowRationalWeight a.val*q))) =
      C (c⁻¹*c⁻¹)*F -
        C ((p:ℚ)^(((i.val+j.val:ℕ):ℤ)-2)*primeLowRationalWeight a.val*q) := by
    rw [mul_sub,← C_mul]
    congr 1
    congr 1
    field_simp [hu.1] <;> ring
  rw [he] at hs
  convert hs using 1 <;> push_cast <;> ring

theorem primeLow_block_scaled_GV (hp4 : 3 < p) (a : Fin (p-4)) (i j : Fin 2) :
    GV p
      (C (primeBlockUnitScale hp4 (Sum.inl (a,i)) *
          primeBlockUnitScale hp4 (Sum.inl (a,j))) *
        primeOriginalNumeratorEntry p (by omega)
          ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,i)))
          ((primeOriginalBlockEquiv hp4).symm (Sum.inl (a,j))) -
        C ((p:ℚ)^((i.val:ℤ)+(j.val:ℤ)-2) *
          primeLowRationalWeight (a.val+1) * lowBlock i j))
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
  unfold primeOriginalNumeratorEntry
  rw [hbI,hbJ]
  let A : Fin p := ⟨a.val+1,by have h := a.isLt; omega⟩
  let ii : Fin (primeMultiplicity p A) := (primeLowBlockJet hp4 a i).2
  let jj : Fin (primeMultiplicity p A) := (primeLowBlockJet hp4 a j).2
  have hA0 : 0 < A.val := by dsimp only [A]; omega
  have hA : A.val ≤ p-4 := by have h := a.isLt; dsimp only [A]; omega
  have h := primeLow_original_scaled_GV hp4 A hA0 hA ii jj
  simpa only [A,ii,jj,primeLowBlockJet,Fin.val_mk,primeBlockWeight,
    primeLowMoment_eq_lowBlock] using h

end
end Li2

end
