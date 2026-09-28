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

end
end Li2

end
