module
public import Li2Unified.Modular.Positive.Packed.P053
public import Li2Unified.Modular.Base.PrimeQEdgeLeading

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

/- Entry integrality is explicit: a unit determinant alone does not supply it. -/
theorem parameterMatrix_scaled_det_GV (lam : ℚ) (corner : Matrix (Fin 6) (Fin 6) ℚ)
    (M : Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X]) (hp4 : 3 < p)
    (hN : ∀ x y, GV p (parameterReferenceMatrix lam p corner x y)
      (primeBlockWeight x + primeBlockWeight y))
    (herr : ∀ x y, GV p (M x y - parameterReferenceMatrix lam p corner x y)
      (primeBlockWeight x + primeBlockWeight y + 1/2)) :
    GV p (C ((p:ℚ)^(2*(p-1)))*M.det -
      C ((parameterReferenceCore lam p corner).det)) 1 := by
  classical
  have hM (x y : PrimeBlockIndex p) : GV p (M x y)
      (primeBlockWeight x + primeBlockWeight y) := by
    have h := ((herr x y).mono (by linarith)).add (hN x y)
    simpa only [sub_add_cancel] using! h
  have hd := det_sub_GV (p := p)
    M (parameterReferenceMatrix lam p corner)
    (primeBlockWeight (p := p)) (primeBlockWeight (p := p)) (1/2)
    hM hN herr
  rw [parameterReferenceMatrix_det lam corner hp4] at hd
  have hs := GV.C_mul (VG.primePow (p := p) (2*((p-1:ℕ):ℤ))) hd
  rw [primeQ_positive_zpow] at hs
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hcancel : (p:ℚ)^(2*(p-1))*(p:ℚ)^(-2*((p-1:ℕ):ℤ)) = 1 := by
    rw [← primeQ_positive_zpow,← zpow_add₀ hpq,
      show (2:ℤ)*((p-1:ℕ):ℤ)+(-2)*((p-1:ℕ):ℤ) = 0 by ring,zpow_zero]
  have he : C ((p:ℚ)^(2*(p-1))) *
      (M.det -
        C ((p:ℚ)^(-2*((p-1:ℕ):ℤ))*(parameterReferenceCore lam p corner).det)) =
      C ((p:ℚ)^(2*(p-1)))*M.det -
        C ((parameterReferenceCore lam p corner).det) := by
    rw [mul_sub,← C_mul,← mul_assoc,hcancel,one_mul]
  rw [he] at hs
  have hhalf : GV p
      (C ((p:ℚ)^(2*(p-1)))*M.det -
        C ((parameterReferenceCore lam p corner).det)) (1/2) := by
    convert hs using 1
    simp only [primeBlockWeight_sum hp4]
    push_cast
    ring
  intro n
  have hn := VG.round_half (p := p)
    (q := (C ((p:ℚ)^(2*(p-1)))*M.det -
      C ((parameterReferenceCore lam p corner).det)).coeff n) (0:ℤ)
    (by simpa using! hhalf n)
  simpa using! hn


end
end Li2Unified.Proofs.PrimeEdge

#print axioms Li2Unified.Proofs.PrimeEdge.parameterMatrix_scaled_det_GV

end


end
