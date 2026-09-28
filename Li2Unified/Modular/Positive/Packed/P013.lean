module
public import Li2Unified.Modular.Positive.Packed.P012
public import Li2Unified.Modular.Base.FieldPoleCompatibility
public import Li2Unified.Modular.Positive.Packed.P010
public import Li2Unified.Modular.Base.PrimePoleExtension

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem general_original_cleared_scaled (n : ℕ) (a : Fin p)
    (hp : 0 < p) (hsq : 4 * n < p * p) :
    ∃ g : PowerSeries ℤ_[p], ∃ r : Fin p → ℤ_[p],
      PowerSeries.IsRestricted 1 g ∧
      primeDiscPolynomialSeries a.val (4 * n) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (integralPoleNumerator (generalPoleCenters (p := p)) g r) =
      PowerSeries.C ((p : ℚ_[p]) ^ matchingCount (4 * n) p a) *
        (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p]) ^ 3 *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (integralNonmatchingDiscPolynomial (p := p) a.val n : PowerSeries ℤ_[p]) ^ 3 := by
  classical
  obtain ⟨g, r, hg, hclear⟩ := general_tail_integral_cleared n a hp hsq
  refine ⟨g, r, hg, ?_⟩
  have hcore :
      (generalMatchingTailPolynomial n a : PowerSeries ℤ_[p]) *
          integralPoleNumerator (generalPoleCenters (p := p)) g r *
          (integralNonmatchingDiscPolynomial (p := p) a.val (4 * n) :
            PowerSeries ℤ_[p]) =
        (integralPoleDenominator (generalPoleCenters (p := p)) :
          PowerSeries ℤ_[p]) *
          (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p]) ^ 2 *
          (integralNonmatchingDiscPolynomial (p := p) a.val n :
            PowerSeries ℤ_[p]) ^ 3 := by
    calc
      _ = ((integralPoleDenominator (generalPoleCenters (p := p)) :
              PowerSeries ℤ_[p]) *
            (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p]) ^ 2 *
            generalNonmatchingQuotient n a) *
          (integralNonmatchingDiscPolynomial (p := p) a.val (4 * n) :
            PowerSeries ℤ_[p]) := by rw [hclear]
      _ = _ := by
        rw [show (integralPoleDenominator (generalPoleCenters (p := p)) :
              PowerSeries ℤ_[p]) *
            (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p]) ^ 2 *
            generalNonmatchingQuotient n a *
            (integralNonmatchingDiscPolynomial (p := p) a.val (4 * n) :
              PowerSeries ℤ_[p]) =
            (integralPoleDenominator (generalPoleCenters (p := p)) :
              PowerSeries ℤ_[p]) *
            (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p]) ^ 2 *
            (generalNonmatchingQuotient n a *
              (integralNonmatchingDiscPolynomial (p := p) a.val (4 * n) :
                PowerSeries ℤ_[p])) by ring]
        rw [generalNonmatchingQuotient_cleared]
  have hmap := congrArg (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])) hcore
  simp only [map_mul, map_pow] at hmap
  have hfield :
      PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
        (integralPoleDenominator (generalPoleCenters (p := p)) :
          PowerSeries ℤ_[p]) =
      (fieldPoleDenominator (generalPoleCenters (p := p)) :
        PowerSeries ℚ_[p]) := by
    rw [← Polynomial.polynomial_map_coe, fieldPoleDenominator_map]
  rw [hfield] at hmap
  rw [general_disc_factorization (4 * n) a,
    generalMatchingDiscPolynomial_split n a]
  simp only [Polynomial.coe_mul, map_mul]
  let M : PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p])
  let T : PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (generalMatchingTailPolynomial n a : PowerSeries ℤ_[p])
  let N₄ : PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (integralNonmatchingDiscPolynomial (p := p) a.val (4 * n) : PowerSeries ℤ_[p])
  let N : PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (integralNonmatchingDiscPolynomial (p := p) a.val n : PowerSeries ℤ_[p])
  let I : PowerSeries ℚ_[p] := PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (integralPoleNumerator (generalPoleCenters (p := p)) g r)
  let D : PowerSeries ℚ_[p] :=
    (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p])
  let K : PowerSeries ℚ_[p] :=
    PowerSeries.C ((p : ℚ_[p]) ^ matchingCount (4 * n) p a)
  have hmap' : T * I * N₄ = D * M ^ 2 * N ^ 3 := hmap
  change K * (M * T) * N₄ * I = K * D * M ^ 3 * N ^ 3
  calc
    _ = K * M * (T * I * N₄) := by ring
    _ = K * M * (D * M ^ 2 * N ^ 3) := by rw [hmap']
    _ = _ := by ring

#print axioms general_original_cleared_scaled

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalPoleScale (n : ℕ) (a : Fin p) : ℚ_[p] :=
  (p : ℚ_[p]) ^ matchingCount (4 * n) p a /
    ((p : ℚ_[p]) ^ matchingCount n p a) ^ 3

theorem generalPoleScale_zpow (n : ℕ) (a : Fin p) (hp : 0 < p) :
    generalPoleScale n a =
      (p : ℚ_[p]) ^ ((matchingCount (4 * n) p a : ℕ) -
        (3 * matchingCount n p a : ℕ) : ℤ) := by
  have hpq : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  rw [zpow_sub₀ hpq]
  simp only [zpow_natCast]
  unfold generalPoleScale
  congr 1
  rw [show 3 * matchingCount n p a = matchingCount n p a * 3 by omega,
    pow_mul]

theorem general_original_integral_cleared (n : ℕ) (a : Fin p)
    (hp : 0 < p) (hsq : 4 * n < p * p) :
    ∃ g : PowerSeries ℤ_[p], ∃ r : Fin p → ℤ_[p],
      PowerSeries.IsRestricted 1 g ∧
      primeDiscPolynomialSeries a.val (4 * n) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (integralPoleNumerator (generalPoleCenters (p := p)) g r) =
      PowerSeries.C (generalPoleScale n a) *
        (fieldPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℚ_[p]) *
        rationalPolynomialSeries
          (((D n) ^ 3).comp (C (p : ℚ) * X - C (a.val : ℚ))) := by
  classical
  obtain ⟨g, r, hg, hclear⟩ := general_original_cleared_scaled n a hp hsq
  refine ⟨g, r, hg, ?_⟩
  have hdn : rationalPolynomialSeries (p := p)
      (((D n) ^ 3).comp (C (p : ℚ) * X - C (a.val : ℚ))) =
      primeDiscPolynomialSeries a.val n ^ 3 := by
    rw [pow_comp]
    exact map_pow (rationalPolynomialSeries (p := p))
      ((D n).comp (C (p : ℚ) * X - C (a.val : ℚ))) 3
  rw [hdn, general_disc_factorization n a]
  have hpq : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hpow : ((p : ℚ_[p]) ^ matchingCount n p a) ^ 3 ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ hpq)
  have hscale : generalPoleScale n a *
      ((p : ℚ_[p]) ^ matchingCount n p a) ^ 3 =
      (p : ℚ_[p]) ^ matchingCount (4 * n) p a := by
    unfold generalPoleScale
    exact div_mul_cancel₀ _ hpow
  have hK : (PowerSeries.C (generalPoleScale n a) : PowerSeries ℚ_[p]) *
      PowerSeries.C ((p : ℚ_[p]) ^ matchingCount n p a) ^ 3 =
      PowerSeries.C ((p : ℚ_[p]) ^ matchingCount (4 * n) p a) := by
    rw [← map_pow, ← map_mul, hscale]
  rw [hclear, ← hK]
  ring

#print axioms generalPoleScale_zpow
#print axioms general_original_integral_cleared

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

theorem pulled_shift_index (p m j : ℕ) (a : Fin p)
    (hp : 0 < p) (hm : m < p * p) (hj : j ≤ m)
    (hmod : j % p = a.val) :
    (j + (p - 1 - a.val) + 1) / p - 1 =
      (generalMatchingPoleIndex p m j a hp hm hj hmod).val := by
  have hdec := pole_index_decompose p j
  rw [hmod] at hdec
  have he : j + (p - 1 - a.val) + 1 = p * (j / p + 1) := by
    rw [Nat.mul_add]
    omega
  rw [he]
  dsimp [generalMatchingPoleIndex]
  rw [Nat.mul_div_cancel_left]
  all_goals simp [hp]

#print axioms pulled_shift_index

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section

theorem matching_shift_mod (p j : ℕ) (a : Fin p)
    (hm : p ∣ j + (p - 1 - a.val) + 1) :
    j % p = a.val := by
  have ha := a.isLt
  have hq : 0 < (j + (p - 1 - a.val) + 1) / p :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hm) (by omega)
  have he : j = p * ((j + (p - 1 - a.val) + 1) / p - 1) + a.val := by
    have ht := Nat.mul_div_cancel' hm
    rw [show (j + (p - 1 - a.val) + 1) / p =
      (j + (p - 1 - a.val) + 1) / p - 1 + 1 by omega,
      Nat.mul_add, Nat.mul_one] at ht
    omega
  rw [he]
  simp [Nat.add_mod, Nat.mod_eq_of_lt ha]

theorem matching_shift_dvd_iff (p j : ℕ) (a : Fin p) :
    p ∣ j + (p - 1 - a.val) + 1 ↔ j % p = a.val := by
  constructor
  · exact matching_shift_mod p j a
  · intro hmod
    have hdec := pole_index_decompose p j
    rw [hmod] at hdec
    have he : j + (p - 1 - a.val) + 1 = p * (j / p + 1) := by
      rw [Nat.mul_add]
      omega
    rw [he]
    exact dvd_mul_right p (j / p + 1)

#print axioms matching_shift_mod
#print axioms matching_shift_dvd_iff

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Finset Li2
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/- The parameter is explicit; no specialization to the negative-half functional. -/
def parameterFourPoleU (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) : (ℤ_[p])[X] :=
  restrictedPoleFunctional
    (fun n => (n+1:ℕ)*integralParameterMoment z hreg n)
    (fun j : Fin 4 => integralUPole z hu.1 hu.2 j.val (by omega)) f r

def parameterFourPoleV (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) : (ℤ_[p])[X] :=
  restrictedPoleFunctional
    (derivativeMoments (integralParameterMoment z hreg))
    (fun j : Fin 4 => integralVPole z hu.1 hu.2 j.val (by omega)) f r

theorem parameterFourPoleU_coeff_bound (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p)
    (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (hr : ∀ i, ‖r i‖ ≤ B) (n : ℕ) :
    ‖(parameterFourPoleU z hu hreg hp4 f r).coeff n‖ ≤ B :=
  restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

theorem parameterFourPoleV_coeff_bound (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p)
    (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (hr : ∀ i, ‖r i‖ ≤ B) (n : ℕ) :
    ‖(parameterFourPoleV z hu hreg hp4 f r).coeff n‖ ≤ B :=
  restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterFourPoleU_coeff_bound

end

end
