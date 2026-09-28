module
public import Li2Unified.Modular.Base.PadicValuationBridge
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Li2Unified.Modular.Positive.Packed.P023
public import Li2Unified.Modular.Positive.Packed.P007
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.MediumFloorSum

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalNormPrimePower_le_of_exponent_le (e : ℤ) (r : ℚ)
    (he : r ≤ (e : ℚ)) :
    ‖(p : ℚ_[p])‖ ^ e ≤ (p : ℝ) ^ (-(r : ℝ)) := by
  have hp0 : 0 < ‖(p : ℚ_[p])‖ := by
    exact norm_pos_iff.mpr (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hp1 : ‖(p : ℚ_[p])‖ ≤ 1 := by
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast] using
      PadicInt.norm_le_one (p : ℤ_[p])
  have hre : (r : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  calc
    _ ≤ ‖(p : ℚ_[p])‖ ^ (r : ℝ) := by
      simpa only [Real.rpow_intCast] using
        (Real.rpow_le_rpow_of_exponent_ge hp0 hp1 hre)
    _ = ((p : ℝ)⁻¹) ^ (r : ℝ) := by rw [Padic.norm_p]
    _ = ((p : ℝ) ^ (r : ℝ))⁻¹ := Real.inv_rpow (by positivity) _
    _ = _ := by rw [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow (by positivity)]

#print axioms generalNormPrimePower_le_of_exponent_le
end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem actual_general_basis_product_GV_of_disc (lam : ℚ) (n : ℕ)
    (hlam : |(lam : ℝ)| < 1) (hsq : 4 * n < p * p) (hpn : p ≤ n)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0))
    (i j : Fin (2 * n)) (r : ℚ)
    (hr : ∀ a : Fin p, r ≤ ((generalDiscBase n a +
      (generalOriginalBasisLocalOrder n hpn i a +
        generalOriginalBasisLocalOrder n hpn j a : ℕ) : ℤ) : ℚ)) :
    GV p (Li2Unified.ParameterFamily.numeratorFunctional lam (4 * n)
      (((D n) ^ 3) * (generalOriginalBasis n hpn i *
        generalOriginalBasis n hpn j).map (Int.castRingHom ℚ))) r := by
  obtain ⟨F, hF, hF0, heq⟩ :=
    actual_general_basis_product_global_field lam n hlam hsq hpn hunit i j
  have hlamNorm : ‖(lam : ℚ_[p])⁻¹‖ ≤ 1 := by
    have hv := Li2.padic_norm_le_one_of_VG
      (Li2.rational_unit_inverse_VG lam hunit.1.1 hunit.1.2)
    simpa only [Rat.cast_inv] using hv
  have hlamPow (a : Fin p) : ‖(lam : ℚ_[p])⁻¹ ^ a.val‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hlamNorm
  intro t
  apply (Li2.VG_iff_padic_norm_le _ r).mpr
  have hmap : ‖((Li2Unified.ParameterFamily.numeratorFunctional lam (4 * n)
      (((D n) ^ 3) * (generalOriginalBasis n hpn i *
        generalOriginalBasis n hpn j).map (Int.castRingHom ℚ))).map
          (Rat.castHom ℚ_[p])).coeff t‖ ≤ (p : ℝ) ^ (-(r : ℝ)) := by
    rw [heq, finset_sum_coeff]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro a _
    rw [coeff_C_mul, norm_mul]
    let m : ℕ := generalOriginalBasisLocalOrder n hpn i a +
      generalOriginalBasisLocalOrder n hpn j a
    calc
      _ ≤ ‖(C ((generalPoleScale n a)⁻¹) * F a).coeff t‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hlamPow a) (norm_nonneg ((C ((generalPoleScale n a)⁻¹) * F a).coeff t))
      _ ≤ ‖(p : ℚ_[p])‖ ^ (generalDiscBase n a + (m : ℤ)) := by
        exact generalPoleLocalCoefficient_bound n a (F a) m t (hF a) (hF0 a)
      _ ≤ (p : ℝ) ^ (-(r : ℝ)) :=
        generalNormPrimePower_le_of_exponent_le _ _ (hr a)
  simpa only [coeff_map, Rat.coe_castHom] using hmap

#print axioms actual_general_basis_product_GV_of_disc
end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalOriginal_pair_disc_weight_bound (n : ℕ) (hpn : p ≤ n)
    (i j : Fin (2 * n)) (a : Fin p) :
    (((generalOriginalRowTwiceWeight n hpn i +
        generalOriginalRowTwiceWeight n hpn j : ℤ) : ℚ) / 2) ≤
      ((generalDiscBase n a +
        (generalOriginalBasisLocalOrder n hpn i a +
          generalOriginalBasisLocalOrder n hpn j a : ℕ) : ℤ) : ℚ) := by
  have hi := generalOriginalRow_disc_bound n hpn i a
  have hj := generalOriginalRow_disc_bound n hpn j a
  have htwice : generalOriginalRowTwiceWeight n hpn i +
      generalOriginalRowTwiceWeight n hpn j ≤
      (generalDiscBase n a +
        (generalOriginalBasisLocalOrder n hpn i a +
          generalOriginalBasisLocalOrder n hpn j a : ℕ) : ℤ) * 2 := by
    omega
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr
  exact_mod_cast htwice

#print axioms generalOriginal_pair_disc_weight_bound
end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem actual_general_original_entry_GV (lam : ℚ) (n : ℕ)
    (hlam : |(lam : ℝ)| < 1) (hsq : 4 * n < p * p) (hpn : p ≤ n)
    (hunit : (lam ≠ 0 ∧ padicValRat p lam = 0) ∧
      (1 - lam ≠ 0 ∧ padicValRat p (1 - lam) = 0))
    (i j : Fin (2 * n)) :
    GV p (Li2Unified.ParameterFamily.numeratorFunctional lam (4 * n)
      ((D n) ^ 3 * (generalOriginalBasis n hpn i).map (Int.castRingHom ℚ) *
        (generalOriginalBasis n hpn j).map (Int.castRingHom ℚ)))
      (((generalOriginalRowTwiceWeight n hpn i : ℚ) +
        (generalOriginalRowTwiceWeight n hpn j : ℚ)) / 2) := by
  have h := actual_general_basis_product_GV_of_disc lam n hlam hsq hpn hunit
    i j (((generalOriginalRowTwiceWeight n hpn i +
      generalOriginalRowTwiceWeight n hpn j : ℤ) : ℚ) / 2)
    (generalOriginal_pair_disc_weight_bound n hpn i j)
  simpa only [Polynomial.map_mul, mul_assoc, Int.cast_add] using h

#print axioms actual_general_original_entry_GV
end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
open Li2Unified.ParameterFamily
variable {p : ℕ} [Fact p.Prime]

theorem actual_binomGram_of_unit_basis (lam : ℚ) (n : ℕ) (hK : 4*n < p^2)
    (E : Fin (2*n) → ℚ[X]) (hE : ∀ i, (E i).natDegree < 2*n)
    (he : (coeffMat E).det ≠ 0) (hev : padicValRat p (coeffMat E).det = 0)
    (r : ℚ)
    (hraw : GV p ((Matrix.of fun i j : Fin (2*n) =>
      numeratorFunctional lam (4*n) ((D n)^3 * E i * E j)).det) r) :
    GV p (ParameterFamily.binomGram lam n).det (r+normVal p n) := by
  rw [original_gram_basis_change lam n E hE] at hraw
  have hu : VG p (((coeffMat E).det^2)⁻¹) 0 := by
    right
    rw [padicValRat.inv, padicValRat.pow, hev]
    norm_num
  have hq := GV.C_mul hu hraw
  have heq : C (((coeffMat E).det^2)⁻¹) *
      (C ((coeffMat E).det^2)*ParameterFamily.Q lam n) = ParameterFamily.Q lam n := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ he), C_1, one_mul]
  rw [heq, zero_add] at hq
  have hscale : VG p (Sn n^(2*n)/Fn n) (normVal p n) := by
    right
    rw [normScale_val p hK]
  have hs := GV.C_mul hscale hq
  rw [← ParameterFamily.Qtilde_eq_binomGram_det]
  simpa only [ParameterFamily.Qtilde, add_comm] using hs

end
end Li2Unified.Proofs.Hermite
#print axioms Li2Unified.Proofs.Hermite.actual_binomGram_of_unit_basis

end

end
