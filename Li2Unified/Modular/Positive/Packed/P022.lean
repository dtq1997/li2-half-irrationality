module
public import Li2Unified.Modular.Positive.Packed.P021
public import Li2Unified.Modular.Base.IntegralPolynomialSubstitution
public import Li2Unified.Modular.Positive.Packed.P016
public import Li2Unified.Modular.Base.ParameterPoleValues

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleTest_U_shift_coeff_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (T : ℤ[X]) (a : Fin p) (eta : ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B)
    (k : ℕ) :
    ‖((generalPoleU z hu hz
      (integralPoleMulRegular (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) f r)
      (integralPoleMulResidue (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r)).comp
          (C ((p : ℤ_[p]) ^ 2) * (X - C eta))).coeff k‖ ≤ B := by
  classical
  exact integralPolynomial_comp_coeff_bound _ _ B hB
    (fun j => generalPoleTest_U_coeff_bound z hu hz f r T a B hB hT j) k

theorem generalPoleTest_V_shift_coeff_bound (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (r : Fin p → ℤ_[p])
    (T : ℤ[X]) (a : Fin p) (eta : ℤ_[p])
    (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B)
    (k : ℕ) :
    ‖((generalPoleV z hu hz
      (integralPoleMulRegular (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) f r)
      (integralPoleMulResidue (generalPoleCenters (p := p))
        (integralDiscTestPolynomial T a : PowerSeries ℤ_[p]) r)).comp
          (C ((p : ℤ_[p]) ^ 2) * (X - C eta))).coeff k‖ ≤ B := by
  classical
  exact integralPolynomial_comp_coeff_bound _ _ B hB
    (fun j => generalPoleTest_V_coeff_bound z hu hz f r T a B hB hT j) k

#print axioms generalPoleTest_U_shift_coeff_bound
#print axioms generalPoleTest_V_shift_coeff_bound

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalPoleDiscFieldUV (a : Fin p) (eta : ℤ_[p])
    (U V : (ℤ_[p])[X]) : (ℚ_[p])[X] :=
  (U.comp (C ((p : ℤ_[p]) ^ 2) * (X - C eta))).map
    (algebraMap ℤ_[p] ℚ_[p]) -
  C ((a.val : ℚ_[p]) / (p : ℚ_[p])) *
    (V.comp (C ((p : ℤ_[p]) ^ 2) * (X - C eta))).map
      (algebraMap ℤ_[p] ℚ_[p])

theorem generalPoleDiscFieldUV_scaled_coeff_bound (a : Fin p)
    (eta : ℤ_[p]) (U V : (ℤ_[p])[X]) (B : ℝ) (hB : 0 ≤ B)
    (hU : ∀ k, ‖U.coeff k‖ ≤ B)
    (hV : ∀ k, ‖V.coeff k‖ ≤ B) (k : ℕ) :
    ‖(C (p : ℚ_[p]) * generalPoleDiscFieldUV a eta U V).coeff k‖ ≤ B := by
  let G : (ℤ_[p])[X] := C ((p : ℤ_[p]) ^ 2) * (X - C eta)
  let u : ℚ_[p] := ((U.comp G).map (algebraMap ℤ_[p] ℚ_[p])).coeff k
  let v : ℚ_[p] := ((V.comp G).map (algebraMap ℤ_[p] ℚ_[p])).coeff k
  have hu : ‖u‖ ≤ B := by
    simpa only [u, coeff_map, PadicInt.norm_def] using!
      (integralPolynomial_comp_coeff_bound U G B hB hU k)
  have hv : ‖v‖ ≤ B := by
    simpa only [v, coeff_map, PadicInt.norm_def] using!
      (integralPolynomial_comp_coeff_bound V G B hB hV k)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpNorm : ‖(p : ℚ_[p])‖ ≤ 1 := by
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast] using
      PadicInt.norm_le_one (p : ℤ_[p])
  have haNorm : ‖(a.val : ℚ_[p])‖ ≤ 1 := by
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast] using
      PadicInt.norm_le_one (a.val : ℤ_[p])
  have he : (C (p : ℚ_[p]) * generalPoleDiscFieldUV a eta U V).coeff k =
      (p : ℚ_[p]) * u - (a.val : ℚ_[p]) * v := by
    simp only [generalPoleDiscFieldUV, coeff_C_mul, coeff_sub, G, u, v]
    field_simp
  rw [he]
  rw [sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · rw [norm_mul]
    calc
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hpNorm (norm_nonneg _)
      _ ≤ B := by simpa using hu
  · rw [norm_neg, norm_mul]
    calc
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right haNorm (norm_nonneg _)
      _ ≤ B := by simpa using hv

#print axioms generalPoleDiscFieldUV_scaled_coeff_bound

theorem generalPoleDiscFieldUV_zero_coeff_bound (a : Fin p)
    (ha : a.val = 0) (eta : ℤ_[p]) (U V : (ℤ_[p])[X])
    (B : ℝ) (hB : 0 ≤ B) (hU : ∀ k, ‖U.coeff k‖ ≤ B)
    (k : ℕ) :
    ‖(generalPoleDiscFieldUV a eta U V).coeff k‖ ≤ B := by
  simp only [generalPoleDiscFieldUV, ha, Nat.cast_zero, zero_div, C_0,
    zero_mul, sub_zero, coeff_map]
  exact integralPolynomial_comp_coeff_bound U
    (C ((p : ℤ_[p]) ^ 2) * (X - C eta)) B hB hU k

#print axioms generalPoleDiscFieldUV_zero_coeff_bound

theorem generalPoleDiscFieldUV_eval (a : Fin p) (eta : ℤ_[p])
    (U V : (ℤ_[p])[X]) (x : ℚ_[p]) :
    (generalPoleDiscFieldUV a eta U V).eval x =
      U.eval₂ (algebraMap ℤ_[p] ℚ_[p])
          ((p : ℚ_[p]) ^ 2 * (x - (eta : ℚ_[p]))) -
        (a.val : ℚ_[p]) / (p : ℚ_[p]) *
          V.eval₂ (algebraMap ℤ_[p] ℚ_[p])
            ((p : ℚ_[p]) ^ 2 * (x - (eta : ℚ_[p]))) := by
  simp only [generalPoleDiscFieldUV, eval_sub, eval_mul, eval_C,
    eval_map, eval₂_comp, eval₂_mul, eval₂_sub, eval₂_C, eval₂_X]
  simp only [PadicInt.algebraMap_apply, PadicInt.coe_pow, PadicInt.coe_natCast]

#print axioms generalPoleDiscFieldUV_eval

end
end Li2Unified.Proofs.Hermite

end

section
open Li2 Li2Unified.Proofs.Hermite
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterPoleEta_norm_le_one (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) :
    ‖parameterPoleEta lam hreg‖ ≤ 1 := by
  have hl : ‖(lam:ℚ_[p])‖ ≤ 1 :=
    padic_norm_le_one_of_VG (Or.inr (by rw [hu.2]; norm_num))
  have hi : ‖(lam:ℚ_[p])⁻¹‖ ≤ 1 := by
    simpa only [Rat.cast_inv] using
      padic_norm_le_one_of_VG (rational_unit_inverse_VG lam hu.1 hu.2)
  unfold parameterPoleEta
  rw [norm_mul, norm_pow]
  apply mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hi) (norm_nonneg _)
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro b hb
  have hbp : b+1 < p := by have := Finset.mem_range.mp hb; omega
  rw [parameterDissectedSquare_nonmatching (lam^p) hreg 0 b
    (Nat.not_dvd_of_pos_of_lt (by omega) hbp), norm_mul, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hl) (norm_nonneg _)
    (PadicInt.norm_le_one _)

def parameterIntegralEta (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) : ℤ_[p] :=
  ⟨parameterPoleEta lam hreg, parameterPoleEta_norm_le_one lam hu hreg⟩

theorem parameterIntegralEta_coe (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) :
    (parameterIntegralEta lam hu hreg : ℚ_[p]) = parameterPoleEta lam hreg := rfl

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterPoleEta_norm_le_one

end

section
open Polynomial Li2
open Li2Unified.Proofs.PrimeEdge
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalPoleScale_ne_zero (n : ℕ) (a : Fin p) :
    generalPoleScale n a ≠ 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold generalPoleScale
  exact div_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ (pow_ne_zero _ hp0))

theorem actual_general_global_field (lam : ℚ) (n : ℕ) (T : ℤ[X])
    (hlam : |(lam : ℝ)| < 1) (hsq : 4 * n < p * p)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0))
    (B : Fin p → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hT : ∀ a k, ‖(integralDiscTestPolynomial T a).coeff k‖ ≤ B a) :
    ∃ F : Fin p → (ℚ_[p])[X],
      (∀ a k, ‖(C (p : ℚ_[p]) * F a).coeff k‖ ≤ B a) ∧
      (∀ a, a.val = 0 → ∀ k, ‖(F a).coeff k‖ ≤ B a) ∧
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4 * n)
          (((D n) ^ 3) * T.map (Int.castRingHom ℚ))).map
          (Rat.castHom ℚ_[p]) =
        ∑ a : Fin p, C ((lam : ℚ_[p])⁻¹ ^ a.val) *
          (C ((generalPoleScale n a)⁻¹) * F a) := by
  classical
  let hu := hunit.1
  let hr := (parameterPoleHypotheses_of_hunit lam hunit).2.2.1
  let eta : ℤ_[p] := parameterIntegralEta lam hu hr
  have hex (a : Fin p) := actual_general_integer_tests_uniform lam n a T
    hsq hunit (B a) (hB a) (hT a)
  choose g r hh using hex
  let U (a : Fin p) := generalPoleU (lam ^ p)
    (Li2Unified.LambdaLift.parameter_power_unit lam hu) hr (g a) (r a)
  let V (a : Fin p) := generalPoleV (lam ^ p)
    (Li2Unified.LambdaLift.parameter_power_unit lam hu) hr (g a) (r a)
  let F (a : Fin p) := generalPoleDiscFieldUV a eta (U a) (V a)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro a k
    exact generalPoleDiscFieldUV_scaled_coeff_bound a eta (U a) (V a)
      (B a) (hB a) (hh a).2.1 (hh a).2.2.1 k
  · intro a ha k
    exact generalPoleDiscFieldUV_zero_coeff_bound a ha eta (U a) (V a)
      (B a) (hB a) (hh a).2.1 k
  · have heval (a : Fin p) (x : ℚ_[p]) :
        (F a).eval x = generalPoleScale n a *
          parameterPulledValue lam hr (parameterPoleShiftY lam hr x) (4 * n)
            (((D n) ^ 3) * T.map (Int.castRingHom ℚ)) a := by
      rw [generalPoleDiscFieldUV_eval]
      have hshift : parameterPoleShiftY lam hr x =
          (p : ℚ_[p]) ^ 2 * (x - (eta : ℚ_[p])) := by
        simp only [parameterPoleShiftY, eta, parameterIntegralEta_coe]
      simpa only [F, U, V, hshift, hu, hr] using
        ((hh a).2.2.2 ((p : ℚ_[p]) ^ 2 * (x - (eta : ℚ_[p])))).symm
    apply Polynomial.funext
    intro x
    rw [eval_map, numeratorFunctional_pulled_eval lam (4 * n)
      (((D n) ^ 3) * T.map (Int.castRingHom ℚ)) hlam hu.1
      (parameterPoleHypotheses_of_hunit lam hunit).2.1 hr
      (parameterPoleHypotheses_of_hunit lam hunit).2.2.2 x]
    simp only [eval_finset_sum, eval_mul, eval_C]
    apply Finset.sum_congr rfl
    intro a ha
    rw [heval a x]
    have hs := generalPoleScale_ne_zero n a
    field_simp

#print axioms generalPoleScale_ne_zero
#print axioms actual_general_global_field

end
end Li2Unified.Proofs.Hermite

end


end
