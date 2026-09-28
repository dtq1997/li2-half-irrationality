module
public import Li2Unified.Modular.Base.RationalPoleParameter
public import Li2Unified.Modular.Base.IntegralPolynomials

set_option backward.privateInPublic true

@[expose] public section

/-! Discharge the coefficient integrality hypotheses for the literal base
shapes and obtain their evaluated congruences at the actual prime parameter. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma zeroShapeRegular_integral (k : Fin 5) : GV p (zeroShapeRegular k) 0 := by
  fin_cases k
  · simpa [zeroShapeRegular] using GV.zero (p := p) 0
  · simpa [zeroShapeRegular] using GV.zero (p := p) 0
  · simpa [zeroShapeRegular] using GV.zero (p := p) 0
  · simpa [zeroShapeRegular] using GV.C (p := p) VG.one
  · simpa [zeroShapeRegular, C_ofNat] using!
      (GV.X (p := p)).sub (GV.C (VG.natCast (p := p) 6))

lemma highShapeRegular_integral (k : Fin 3) : GV p (highShapeRegular k) 0 := by
  fin_cases k
  · simpa [highShapeRegular] using GV.C (p := p) VG.one
  · simpa [highShapeRegular, C_ofNat] using!
      (GV.X (p := p)).sub (GV.C (VG.natCast (p := p) 3))
  · have hx2 : GV p (X^2:ℚ[X]) 0 := by simpa using (GV.X (p := p)).pow 2
    have h3x : GV p (C 3*X:ℚ[X]) 0 := by
      simpa using (GV.C (VG.natCast (p := p) 3)).mul GV.X
    simpa [highShapeRegular, C_ofNat] using! (hx2.sub h3x).add (GV.C (VG.natCast (p := p) 7))

lemma zeroShapeResidue_integral (hp4 : 3 < p) (k : Fin 5) (j : Fin 4) :
    VG p (zeroShapeResidue k j) 0 := by
  have hhalf : VG p (1/2:ℚ) 0 := by
    simpa using rational_unit_inverse_VG (p := p) (2:ℚ) (by norm_num)
      (two_valuation_zero (by omega))
  have hint (a : ℤ) : VG p ((a:ℚ)^k.val) 0 := by
    simpa using (VG.intCast (p := p) a).pow k.val
  fin_cases j
  · simpa [zeroShapeResidue] using VG.zero (p := p) 0
  · simpa [zeroShapeResidue] using hhalf.mul (hint (-1))
  · simpa [zeroShapeResidue] using (hint (-2)).neg
  · simpa [zeroShapeResidue] using hhalf.mul (hint (-3))

lemma highShapeResidue_integral (k : Fin 3) (j : Fin 4) :
    VG p (highShapeResidue k j) 0 := by
  have hint (a : ℤ) : VG p ((a:ℚ)^k.val) 0 := by
    simpa using (VG.intCast (p := p) a).pow k.val
  fin_cases j
  · simpa [highShapeResidue] using VG.zero (p := p) 0
  · simpa [highShapeResidue] using hint (-1)
  · simpa [highShapeResidue] using (VG.intCast (p := p) (-4)).mul (hint (-2))
  · simpa [highShapeResidue] using VG.zero (p := p) 0

theorem zeroShape_U_prime_values (hp4 : 3 < p) (k : Fin 5) :
    VG p ((rationalPoleU (primeParameter p) (zeroShapeRegular k) (zeroShapeResidue k)).eval 0 -
      ![-113/12,95/4,-253/4,2093/12,-17773/36] k) 1 := by
  have h := rationalPoleU_prime_congr hp4 _ _ (zeroShapeRegular_integral k)
    (zeroShapeResidue_integral hp4 k)
  simpa only [coeff_sub, coeff_zero_eq_eval_zero, eval_sub, zeroShape_U_values] using h 0

theorem lowShape_V_prime_values (hp4 : 3 < p) (k : Fin 3) :
    VG p ((rationalPoleV (primeParameter p)
      (zeroShapeRegular ⟨k.val+2,by omega⟩) (zeroShapeResidue ⟨k.val+2,by omega⟩)).eval 0 -
      ![95/4,-253/4,2093/12] k) 1 := by
  have h := rationalPoleV_prime_congr hp4 _ _
    (zeroShapeRegular_integral (⟨k.val+2,by omega⟩ : Fin 5))
    (zeroShapeResidue_integral hp4 ⟨k.val+2,by omega⟩)
  simpa only [coeff_sub, coeff_zero_eq_eval_zero, eval_sub, lowShape_V_values] using h 0

theorem highShape_V_prime_values (hp4 : 3 < p) (k : Fin 3) :
    VG p ((rationalPoleV (primeParameter p) (highShapeRegular k) (highShapeResidue k)).eval 0 -
      ![8,-46/3,266/9] k) 1 := by
  have h := rationalPoleV_prime_congr hp4 _ _ (highShapeRegular_integral k)
    (highShapeResidue_integral (p := p) k)
  simpa only [coeff_sub, coeff_zero_eq_eval_zero, eval_sub, highShape_V_values] using h 0

end
end Li2

end
