module
public import Li2Unified.Modular.Base.PrimeBasis
public import Li2Unified.Modular.Base.ClassBasisJets
public import Li2Unified.Modular.Base.IntegralPolynomials

set_option backward.privateInPublic true

@[expose] public section

/-! Literal local expansions of the Li2 prime-edge product basis. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def primeDiscSubstitution (p : ℕ) (a : Fin p) : ℤ[X] :=
  C (primeCenter p a) + C (p:ℤ)*X

def primeLocalUnit (p : ℕ) (a : Fin p) : ℤ :=
  (classProduct (primeCenter p) (primeMultiplicity p) a).eval (primeCenter p a)

theorem primeLocalUnit_mod_ne_zero (p : ℕ) [Fact p.Prime] (a : Fin p) :
    (primeLocalUnit p a : ZMod p) ≠ 0 := by
  have h := classProduct_eval_ne_zero (fun a => (primeCenter p a : ZMod p))
    (primeCenter_mod_injective p) (primeMultiplicity p) a
  simpa only [primeLocalUnit, classProduct, eval_prod, eval_pow, eval_sub, eval_X, eval_C,
    Int.cast_prod, Int.cast_pow, Int.cast_sub] using h

theorem primeLocalUnit_unit (p : ℕ) [Fact p.Prime] (a : Fin p) :
    (primeLocalUnit p a : ℚ) ≠ 0 ∧ padicValRat p (primeLocalUnit p a : ℚ) = 0 := by
  have hnd : ¬ (p:ℤ) ∣ primeLocalUnit p a := by
    intro h
    exact primeLocalUnit_mod_ne_zero p a ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
  constructor
  · intro h
    have he : primeLocalUnit p a = 0 := by exact_mod_cast h
    exact hnd (he ▸ dvd_zero _)
  · rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hnd]
    rfl

theorem primeJetPoly_own_expansion (p : ℕ) (a : PrimeJet p) :
    ∃ A : ℤ[X], (primeJetPoly p a).comp (primeDiscSubstitution p a.1) =
      C ((p:ℤ)^a.2.val)*X^a.2.val*(C (primeLocalUnit p a.1)+C (p:ℤ)*A) :=
  classBasisPoly_own_expansion _ _ _ _ _

theorem primeJetPoly_other_expansion (p : ℕ) (a : PrimeJet p) (b : Fin p) (hb : b ≠ a.1) :
    ∃ A : ℤ[X], (primeJetPoly p a).comp (primeDiscSubstitution p b) =
      C ((p:ℤ)^(primeMultiplicity p b))*X^(primeMultiplicity p b)*A :=
  classBasisPoly_other_expansion _ _ _ _ _ _ hb

theorem primeProduct_expansion (p : ℕ) (a : Fin p) :
    ∃ A : ℤ[X], (primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^(primeMultiplicity p a))*X^(primeMultiplicity p a)*
        (C (primeLocalUnit p a)+C (p:ℤ)*A) :=
  fullClassProduct_expansion _ _ _ _

lemma GV.integer_polynomial (p : ℕ) (P : ℤ[X]) :
    GV p (P.map (Int.castRingHom ℚ)) 0 := by
  intro k
  rw [coeff_map]
  exact VG.intCast _

lemma integer_polynomial_pmultiple_VG (p m : ℕ) [Fact p.Prime] (P : ℤ[X])
    (h : ∃ A : ℤ[X], P = C ((p:ℤ)^m)*A) :
    GV p (P.map (Int.castRingHom ℚ)) (m:ℚ) := by
  obtain ⟨A, rfl⟩ := h
  simp only [Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom, Int.cast_pow,
    Int.cast_natCast]
  have hp : VG p ((p:ℚ)^m) (m:ℚ) := by
    simpa only [zpow_natCast, Int.cast_natCast] using VG.primePow (p := p) (m:ℤ)
  simpa only [add_zero] using GV.C_mul hp (GV.integer_polynomial p A)

theorem primeJetPoly_other_VG (p : ℕ) [Fact p.Prime] (a : PrimeJet p) (b : Fin p)
    (hb : b ≠ a.1) :
    GV p (((primeJetPoly p a).comp (primeDiscSubstitution p b)).map (Int.castRingHom ℚ))
      (primeMultiplicity p b : ℚ) := by
  obtain ⟨A, hA⟩ := primeJetPoly_other_expansion p a b hb
  apply integer_polynomial_pmultiple_VG
  exact ⟨X^(primeMultiplicity p b)*A, by rw [hA, mul_assoc]⟩

theorem primeJetPoly_own_error_VG (p : ℕ) [Fact p.Prime] (a : PrimeJet p) :
    GV p (((primeJetPoly p a).comp (primeDiscSubstitution p a.1) -
      C ((p:ℤ)^a.2.val)*X^a.2.val*C (primeLocalUnit p a.1)).map (Int.castRingHom ℚ))
      ((a.2.val:ℚ)+1) := by
  obtain ⟨A, hA⟩ := primeJetPoly_own_expansion p a
  have h : ∃ B : ℤ[X],
      (primeJetPoly p a).comp (primeDiscSubstitution p a.1) -
        C ((p:ℤ)^a.2.val)*X^a.2.val*C (primeLocalUnit p a.1) =
        C ((p:ℤ)^(a.2.val+1))*B := by
    refine ⟨X^a.2.val*A, ?_⟩
    rw [hA, pow_succ, C_mul]
    ring
  simpa only [Nat.cast_add, Nat.cast_one] using integer_polynomial_pmultiple_VG p _ _ h

theorem primeProduct_error_VG (p : ℕ) [Fact p.Prime] (a : Fin p) :
    GV p (((primeProduct p).comp (primeDiscSubstitution p a) -
      C ((p:ℤ)^(primeMultiplicity p a))*X^(primeMultiplicity p a)*C (primeLocalUnit p a)).map
        (Int.castRingHom ℚ)) ((primeMultiplicity p a : ℚ)+1) := by
  obtain ⟨A, hA⟩ := primeProduct_expansion p a
  have h : ∃ B : ℤ[X],
      (primeProduct p).comp (primeDiscSubstitution p a) -
        C ((p:ℤ)^(primeMultiplicity p a))*X^(primeMultiplicity p a)*C (primeLocalUnit p a) =
        C ((p:ℤ)^(primeMultiplicity p a+1))*B := by
    refine ⟨X^(primeMultiplicity p a)*A, ?_⟩
    rw [hA, pow_succ, C_mul]
    ring
  simpa only [Nat.cast_add, Nat.cast_one] using integer_polynomial_pmultiple_VG p _ _ h

end
end Li2

end
