module
public import Li2Unified.Modular.Base.PrimeReferenceDeterminant
public import Li2Unified.Modular.Base.PrimeReferenceBounds
public import Li2Unified.Modular.Base.DetCongruence
public import Li2Unified.Modular.Base.PrimitiveReduction

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeQ_positive_zpow :
    (p:ℚ)^(2*((p-1:ℕ):ℤ)) = (p:ℚ)^(2*(p-1)) := by
  rw [show (2:ℤ)*((p-1:ℕ):ℤ) = ((2*(p-1):ℕ):ℤ) by push_cast <;> ring]
  rw [zpow_natCast]

theorem primeNormalizedMatrix_scaled_det_GV (hp4 : 3 < p) :
    GV p (C ((p:ℚ)^(2*(p-1)))*(primeNormalizedMatrix hp4).det -
      C (primeReferenceMainConstant p)) 1 := by
  classical
  have hd := det_sub_GV (p := p)
    (primeNormalizedMatrix hp4) (primeReferenceMatrix p)
    (primeBlockWeight (p := p)) (primeBlockWeight (p := p)) (1/2)
    (primeNormalizedMatrix_GV hp4) (primeReferenceMatrix_GV hp4)
    (primeReference_entry_GV hp4)
  rw [primeReferenceMatrix_det hp4] at hd
  have hs := GV.C_mul (VG.primePow (p := p) (2*((p-1:ℕ):ℤ))) hd
  rw [primeQ_positive_zpow] at hs
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hcancel : (p:ℚ)^(2*(p-1))*(p:ℚ)^(-2*((p-1:ℕ):ℤ)) = 1 := by
    rw [← primeQ_positive_zpow,← zpow_add₀ hpq,
      show (2:ℤ)*((p-1:ℕ):ℤ)+(-2)*((p-1:ℕ):ℤ) = 0 by ring,zpow_zero]
  have he : C ((p:ℚ)^(2*(p-1))) *
      ((primeNormalizedMatrix hp4).det -
        C ((p:ℚ)^(-2*((p-1:ℕ):ℤ))*primeReferenceMainConstant p)) =
      C ((p:ℚ)^(2*(p-1)))*(primeNormalizedMatrix hp4).det -
        C (primeReferenceMainConstant p) := by
    rw [mul_sub,← C_mul,← mul_assoc,hcancel,one_mul]
  rw [he] at hs
  have hhalf : GV p
      (C ((p:ℚ)^(2*(p-1)))*(primeNormalizedMatrix hp4).det -
        C (primeReferenceMainConstant p)) (1/2) := by
    convert hs using 1
    simp only [primeBlockWeight_sum hp4]
    push_cast
    ring
  intro n
  have hn := VG.round_half (p := p)
    (q := (C ((p:ℚ)^(2*(p-1)))*(primeNormalizedMatrix hp4).det -
      C (primeReferenceMainConstant p)).coeff n) (0:ℤ)
    (by simpa using hhalf n)
  simpa using hn

def primeQEdgeScale (hp4 : 3 < p) : ℚ :=
  (p:ℚ)^(2*(p-1))*primeNormalizedDetScale hp4

lemma primeQEdgeScale_spec (hp4 : 3 < p) :
    primeQEdgeScale hp4 ≠ 0 ∧
      padicValRat p (primeQEdgeScale hp4) = 2*((p-1:ℕ):ℤ) := by
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu := primeNormalizedDetScale_unit hp4
  unfold primeQEdgeScale
  refine ⟨mul_ne_zero (pow_ne_zero _ hpq) hu.1, ?_⟩
  rw [padicValRat.mul (pow_ne_zero _ hpq) hu.1,
    padicValRat.pow hpq,padicValRat.self hp.out.one_lt,hu.2]
  push_cast
  ring

theorem primeQ_scaled_congruence (hp4 : 3 < p) :
    GV p (C (primeQEdgeScale hp4)*Q (p-1)-C (primeReferenceMainConstant p)) 1 := by
  have h := primeNormalizedMatrix_scaled_det_GV hp4
  rw [primeNormalizedMatrix_det_eq_Q hp4] at h
  simpa only [primeQEdgeScale,← mul_assoc,← C_mul] using h

lemma primeQ_scaled_constant_unit (hp73 : 73 < p) :
    primeQEdgeScale (p := p) (by omega)*(Q (p-1)).coeff 0 ≠ 0 ∧
      padicValRat p (primeQEdgeScale (p := p) (by omega)*(Q (p-1)).coeff 0) = 0 := by
  have hc := primeReferenceMainConstant_unit (p := p) hp73
  apply unit_of_VG_sub hc.1 hc.2
  simpa only [coeff_sub,coeff_C_mul,coeff_C_zero] using
    primeQ_scaled_congruence (p := p) (by omega) 0

theorem primeQ_ne_zero (hp73 : 73 < p) : Q (p-1) ≠ 0 := by
  intro hQ
  have h := (primeQ_scaled_constant_unit (p := p) hp73).1
  apply h
  simp only [hQ,coeff_zero,mul_zero]

theorem primeQ_strict_edge (hp73 : 73 < p) :
    (Q (p-1)).coeff 0 ≠ 0 ∧
      padicValRat p ((Q (p-1)).coeff 0) = -2*((p-1:ℕ):ℤ) ∧
      ∀ k, k ≠ 0 → (Q (p-1)).coeff k = 0 ∨
        -2*((p-1:ℕ):ℤ) < padicValRat p ((Q (p-1)).coeff k) := by
  have hp4 : 3 < p := by omega
  have hs := primeQEdgeScale_spec (p := p) hp4
  have hu := primeQ_scaled_constant_unit (p := p) hp73
  have hq0 : (Q (p-1)).coeff 0 ≠ 0 := by
    intro h0
    exact hu.1 (by rw [h0,mul_zero])
  have hv0 := padicValRat.mul (p := p) hs.1 hq0
  rw [hu.2,hs.2] at hv0
  have h0val : padicValRat p ((Q (p-1)).coeff 0) = -2*((p-1:ℕ):ℤ) := by omega
  refine ⟨hq0,h0val,?_⟩
  intro k hk
  by_cases hqk : (Q (p-1)).coeff k = 0
  · exact Or.inl hqk
  · right
    have hvk : VG p (primeQEdgeScale hp4*(Q (p-1)).coeff k) 1 := by
      simpa only [coeff_sub,coeff_C_mul,coeff_C_ne_zero hk,sub_zero] using
        primeQ_scaled_congruence (p := p) hp4 k
    have hb := hvk.resolve_left (mul_ne_zero hs.1 hqk)
    rw [padicValRat.mul hs.1 hqk,hs.2] at hb
    have hlt : ((-2*((p-1:ℕ):ℤ):ℤ):ℚ) <
        (padicValRat p ((Q (p-1)).coeff k):ℚ) := by
      push_cast at hb ⊢
      linarith
    exact_mod_cast hlt

end
end Li2

end
