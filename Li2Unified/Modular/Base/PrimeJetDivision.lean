module
public import Li2Unified.Modular.Base.PrimeScaledJetError

set_option backward.privateInPublic true

@[expose] public section

/-! Dividing pU-aV by p loses exactly one order in its coefficient bound. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma fieldPolynomial_div_prime_bound (F : (ℚ_[p])[X]) (m : ℕ)
    (hF : ∀ n, ‖F.coeff n‖ ≤ ‖(p:ℚ_[p])‖^(m+1)) (n : ℕ) :
    ‖(C ((p:ℚ_[p])⁻¹)*F).coeff n‖ ≤ ‖(p:ℚ_[p])‖^m := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn0 : ‖(p:ℚ_[p])‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  rw [coeff_C_mul,norm_mul,norm_inv]
  calc
    _ ≤ ‖(p:ℚ_[p])‖⁻¹*‖(p:ℚ_[p])‖^(m+1) :=
      mul_le_mul_of_nonneg_left (hF n) (inv_nonneg.mpr (norm_nonneg _))
    _ = _ := by rw [pow_succ]; field_simp

lemma polynomial_divide_scaled_UV (U V H K : (ℚ_[p])[X]) (a q : ℚ_[p]) :
    C ((p:ℚ_[p])⁻¹)*((C (p:ℚ_[p])*U-C a*V)-C q*(C (p:ℚ_[p])*H-C a*K)) =
      (U-C (a/(p:ℚ_[p]))*V)-C q*(H-C (a/(p:ℚ_[p]))*K) := by
  have hp0 : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc : C ((p:ℚ_[p])⁻¹)*C (p:ℚ_[p]) = (1:(ℚ_[p])[X]) := by
    rw [← C_mul,inv_mul_cancel₀ hp0,C_1]
  have hd : C ((p:ℚ_[p])⁻¹)*C a = (C (a/(p:ℚ_[p])) : (ℚ_[p])[X]) := by
    rw [← C_mul]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  calc
    _ = (C ((p:ℚ_[p])⁻¹)*C (p:ℚ_[p]))*(U-C q*H)-
        (C ((p:ℚ_[p])⁻¹)*C a)*(V-C q*K) := by ring
    _ = _ := by rw [hc,hd]; ring

end
end Li2

end
