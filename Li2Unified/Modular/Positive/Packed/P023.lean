module
public import Li2Unified.Modular.Positive.Packed.P007
public import Li2Unified.Modular.Positive.Packed.P022
public import Li2Unified.Modular.Base.PrimeIntegralJetBounds

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalOriginalBasisProduct_integral_bound (n : ℕ) (hpn : p ≤ n)
    (i j : Fin (2 * n)) (a : Fin p) (k : ℕ) :
    ‖(integralDiscTestPolynomial
        (generalOriginalBasis n hpn i * generalOriginalBasis n hpn j) a).coeff k‖ ≤
      ‖(p : ℤ_[p]) ^ (generalOriginalBasisLocalOrder n hpn i a +
        generalOriginalBasisLocalOrder n hpn j a)‖ := by
  obtain ⟨A, hA⟩ := generalOriginalBasisProduct_disc_factor n hpn i j a
  apply Li2.integralDiscTestPolynomial_factor_bound
  exact ⟨X ^ (generalOriginalBasisLocalOrder n hpn i a +
    generalOriginalBasisLocalOrder n hpn j a) * A, by rw [hA, mul_assoc]⟩

theorem actual_general_basis_product_global_field (lam : ℚ) (n : ℕ)
    (hlam : |(lam : ℝ)| < 1) (hsq : 4 * n < p * p) (hpn : p ≤ n)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0))
    (i j : Fin (2 * n)) :
    ∃ F : Fin p → (ℚ_[p])[X],
      (∀ a k, ‖(C (p : ℚ_[p]) * F a).coeff k‖ ≤
        ‖(p : ℤ_[p]) ^ (generalOriginalBasisLocalOrder n hpn i a +
          generalOriginalBasisLocalOrder n hpn j a)‖) ∧
      (∀ a, a.val = 0 → ∀ k, ‖(F a).coeff k‖ ≤
        ‖(p : ℤ_[p]) ^ (generalOriginalBasisLocalOrder n hpn i a +
          generalOriginalBasisLocalOrder n hpn j a)‖) ∧
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4 * n)
          (((D n) ^ 3) * (generalOriginalBasis n hpn i *
            generalOriginalBasis n hpn j).map (Int.castRingHom ℚ))).map
          (Rat.castHom ℚ_[p]) =
        ∑ a : Fin p, C ((lam : ℚ_[p])⁻¹ ^ a.val) *
          (C ((generalPoleScale n a)⁻¹) * F a) := by
  apply actual_general_global_field lam n _ hlam hsq hunit
    (fun a => ‖(p : ℤ_[p]) ^ (generalOriginalBasisLocalOrder n hpn i a +
      generalOriginalBasisLocalOrder n hpn j a)‖)
  · intro a
    exact norm_nonneg _
  · intro a k
    exact generalOriginalBasisProduct_integral_bound n hpn i j a k

#print axioms generalOriginalBasisProduct_integral_bound
#print axioms actual_general_basis_product_global_field

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleField_coeff_bound (n : ℕ) (a : Fin p)
    (F : (ℚ_[p])[X]) (B : ℝ)
    (hF : ∀ k, ‖(C (p : ℚ_[p]) * F).coeff k‖ ≤ B) (k : ℕ) :
    ‖(C ((generalPoleScale n a)⁻¹) * F).coeff k‖ ≤
      ‖(generalPoleScale n a)⁻¹‖ * ‖(p : ℚ_[p])⁻¹‖ * B := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : F.coeff k = (p : ℚ_[p])⁻¹ * (C (p : ℚ_[p]) * F).coeff k := by
    rw [coeff_C_mul]
    field_simp
  calc
    _ = ‖(generalPoleScale n a)⁻¹‖ * ‖(p : ℚ_[p])⁻¹‖ *
        ‖(C (p : ℚ_[p]) * F).coeff k‖ := by
      rw [coeff_C_mul, he, norm_mul, norm_mul]
      ring
    _ ≤ ‖(generalPoleScale n a)⁻¹‖ * ‖(p : ℚ_[p])⁻¹‖ * B :=
      mul_le_mul_of_nonneg_left (hF k)
        (mul_nonneg (norm_nonneg ((generalPoleScale n a)⁻¹))
          (norm_nonneg ((p : ℚ_[p])⁻¹)))

theorem generalPoleField_zero_coeff_bound (n : ℕ) (a : Fin p)
    (F : (ℚ_[p])[X]) (B : ℝ)
    (hF : ∀ k, ‖F.coeff k‖ ≤ B) (k : ℕ) :
    ‖(C ((generalPoleScale n a)⁻¹) * F).coeff k‖ ≤
      ‖(generalPoleScale n a)⁻¹‖ * B := by
  rw [coeff_C_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hF k) (norm_nonneg _)

#print axioms generalPoleField_coeff_bound
#print axioms generalPoleField_zero_coeff_bound
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleScale_inverse_norm (n : ℕ) (a : Fin p) :
    ‖(generalPoleScale n a)⁻¹‖ =
      ‖(p : ℚ_[p])‖ ^ ((3 * matchingCount n p a : ℕ) -
        (matchingCount (4 * n) p a : ℕ) : ℤ) := by
  rw [generalPoleScale_zpow n a (Fact.out : p.Prime).pos]
  rw [norm_inv, norm_zpow]
  rw [← zpow_neg]
  congr 1
  omega

#print axioms generalPoleScale_inverse_norm
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPadicInt_prime_pow_norm (k : ℕ) :
    ‖(p : ℤ_[p]) ^ k‖ = ‖(p : ℚ_[p])‖ ^ k := by
  simp only [norm_pow, PadicInt.norm_def, PadicInt.coe_natCast]

theorem generalScale_norm_nonzero (n : ℕ) (a : Fin p) (k : ℕ) :
    ‖(generalPoleScale n a)⁻¹‖ * ‖(p : ℚ_[p])⁻¹‖ *
        ‖(p : ℤ_[p]) ^ k‖ =
      ‖(p : ℚ_[p])‖ ^
        ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℕ) - 1 + (k : ℤ)) := by
  have hp0 : ‖(p : ℚ_[p])‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [generalPoleScale_inverse_norm, norm_inv,
    generalPadicInt_prime_pow_norm]
  calc
    _ = ‖(p : ℚ_[p])‖ ^ ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℕ) : ℤ) *
        ‖(p : ℚ_[p])‖ ^ (-1 : ℤ) *
        ‖(p : ℚ_[p])‖ ^ (k : ℤ) := by
      simp only [zpow_neg, zpow_one, zpow_natCast]
    _ = _ := by
      rw [← zpow_add₀ hp0, ← zpow_add₀ hp0]
      congr 1

theorem generalScale_norm_zero (n : ℕ) (a : Fin p) (k : ℕ) :
    ‖(generalPoleScale n a)⁻¹‖ * ‖(p : ℤ_[p]) ^ k‖ =
      ‖(p : ℚ_[p])‖ ^
        ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℕ) + (k : ℤ)) := by
  have hp0 : ‖(p : ℚ_[p])‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [generalPoleScale_inverse_norm, generalPadicInt_prime_pow_norm]
  calc
    _ = ‖(p : ℚ_[p])‖ ^ ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℕ) : ℤ) *
        ‖(p : ℚ_[p])‖ ^ (k : ℤ) := by simp only [zpow_natCast]
    _ = _ := by
      rw [← zpow_add₀ hp0]

#print axioms generalPadicInt_prime_pow_norm
#print axioms generalScale_norm_nonzero
#print axioms generalScale_norm_zero
end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleLocalCoefficient_bound (n : ℕ) (a : Fin p)
    (F : (ℚ_[p])[X]) (m t : ℕ)
    (hF : ∀ k, ‖(C (p : ℚ_[p]) * F).coeff k‖ ≤ ‖(p : ℤ_[p]) ^ m‖)
    (hF0 : a.val = 0 → ∀ k, ‖F.coeff k‖ ≤ ‖(p : ℤ_[p]) ^ m‖) :
    ‖(C ((generalPoleScale n a)⁻¹) * F).coeff t‖ ≤
      ‖(p : ℚ_[p])‖ ^ (generalDiscBase n a + (m : ℤ)) := by
  by_cases ha : a.val = 0
  · have h := generalPoleField_zero_coeff_bound n a F _ (hF0 ha) t
    rw [generalScale_norm_zero] at h
    have he : generalDiscBase n a + (m : ℤ) =
        ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℕ) + (m : ℤ)) := by
      simp only [generalDiscBase, if_pos ha, sub_zero]
      omega
    rw [he]
    exact h
  · have h := generalPoleField_coeff_bound n a F _ hF t
    rw [generalScale_norm_nonzero] at h
    have he : generalDiscBase n a + (m : ℤ) =
        ((3 * matchingCount n p a : ℕ) -
          (matchingCount (4 * n) p a : ℕ) - 1 + (m : ℤ)) := by
      simp only [generalDiscBase, if_neg ha]
      omega
    rw [he]
    exact h

#print axioms generalPoleLocalCoefficient_bound
end
end Li2Unified.Proofs.Hermite

end


end
