module
public import Li2Unified.Modular.Base.RationalPoleCongruence

set_option backward.privateInPublic true

@[expose] public section

/-! Every coefficient of the rational four-pole functional is congruent at
z=(-1/2)^p and z=-1/2, for p-integral regular part and residues. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma GV.mul_congr {A B C D : ℚ[X]} {s : ℚ}
    (hC : GV p C 0) (hB : GV p B 0)
    (hAB : GV p (A-B) s) (hCD : GV p (C-D) s) : GV p (A*C-B*D) s := by
  rw [show A*C-B*D = (A-B)*C+B*(C-D) by ring]
  have hleft : GV p ((A-B)*C) s := by simpa using hAB.mul hC
  have hright : GV p (B*(C-D)) s := by simpa using hB.mul hCD
  exact hleft.add hright

lemma rationalPoleTerm_prime_congr (hp4 : 3 < p) (a : ℚ) (ha : VG p a 0)
    (j : ℕ) (hj : j < p) :
    GV p (C (a*(primeParameter p)⁻¹^j)*(X-C (parameterTau (primeParameter p) j)) -
      C (a*(-1/2:ℚ)⁻¹^j)*(X-C (parameterTau (-1/2) j))) 1 := by
  have hi : VG p ((-1/2:ℚ)⁻¹^j) 0 := by
    convert (VG.intCast (p := p) ((-2:ℤ)^j)) using 1 <;> norm_num
  apply GV.mul_congr
  · exact GV.X.sub (GV.C (parameterTau_VG _ (primeParameter_integral (by omega)) j hj))
  · exact GV.C (by simpa using ha.mul hi)
  · rw [← map_sub, ← mul_sub]
    exact GV.C (by simpa using ha.mul (primeParameter_inverse_pow_congr (by omega) j))
  · have h := GV.C (primeParameter_tau_congr (p := p) (by omega) j hj).neg
    convert h using 1 <;> simp only [map_neg, map_sub] <;> ring

theorem rationalPoleU_prime_congr (hp4 : 3 < p) (f : ℚ[X]) (r : Fin 4 → ℚ)
    (hf : GV p f 0) (hr : ∀ j, VG p (r j) 0) :
    GV p (rationalPoleU (primeParameter p) f r-rationalPoleU (-1/2) f r) 1 := by
  unfold rationalPoleU
  rw [add_sub_add_comm, ← map_sub, ← Finset.sum_sub_distrib]
  apply (GV.C (parameterU_prime_congr hp4 f hf)).add
  apply GV.sum
  intro j _
  exact rationalPoleTerm_prime_congr hp4 (r j*(j.val:ℚ))
    (by simpa using (hr j).mul (VG.natCast (p := p) j.val)) j.val (by omega)

theorem rationalPoleV_prime_congr (hp4 : 3 < p) (f : ℚ[X]) (r : Fin 4 → ℚ)
    (hf : GV p f 0) (hr : ∀ j, VG p (r j) 0) :
    GV p (rationalPoleV (primeParameter p) f r-rationalPoleV (-1/2) f r) 1 := by
  unfold rationalPoleV
  rw [add_sub_add_comm, ← map_sub, ← Finset.sum_sub_distrib]
  apply (GV.C (parameterV_prime_congr hp4 f hf)).add
  apply GV.sum
  intro j _
  exact rationalPoleTerm_prime_congr hp4 (-r j) (hr j).neg j.val (by omega)

end
end Li2

end
