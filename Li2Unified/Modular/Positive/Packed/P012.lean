module
public import Li2Unified.Modular.Positive.Packed.P011
public import Li2Unified.Modular.Base.PrimeDiscShapes
public import Li2Unified.Modular.Base.PrimeDiscUnits

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalMatchingDiscPolynomial (m : ℕ) (a : Fin p) : (ℤ_[p])[X] :=
  ∏ j ∈ (Finset.Icc 1 m).filter (fun j => j % p = a.val),
    (X + C ((j / p : ℕ) : ℤ_[p]))

theorem generalMatchingDiscPolynomial_split (n : ℕ) (a : Fin p) :
    generalMatchingDiscPolynomial (4 * n) a =
      generalMatchingDiscPolynomial n a * generalMatchingTailPolynomial n a := by
  classical
  let s := (Finset.Icc 1 n).filter (fun j => j % p = a.val)
  let t := (Finset.Icc (n + 1) (4 * n)).filter (fun j => j % p = a.val)
  have hs : (Finset.Icc 1 (4 * n)).filter (fun j => j % p = a.val) = s ∪ t := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, s, t]
    constructor <;> intro h <;> omega
  have hd : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_Icc, s, t] at hj hj'
    omega
  unfold generalMatchingDiscPolynomial generalMatchingTailPolynomial
  rw [hs, Finset.prod_union hd]

theorem generalMatchingDiscFactor_scaled (j : ℕ) (a : Fin p)
    (hmod : j % p = a.val) :
    (C (p : ℚ_[p]) * X + C ((j : ℚ_[p]) - (a.val : ℚ_[p])) : (ℚ_[p])[X]) =
      C (p : ℚ_[p]) * (X + C ((j / p : ℕ) : ℚ_[p])) := by
  have hdec := pole_index_decompose p j
  rw [hmod] at hdec
  have hc : (j : ℚ_[p]) =
      (a.val : ℚ_[p]) + (p : ℚ_[p]) * (j / p : ℕ) := by
    exact_mod_cast hdec
  have hsub : (j : ℚ_[p]) - (a.val : ℚ_[p]) =
      (p : ℚ_[p]) * (j / p : ℕ) := by
    linear_combination hc
  rw [hsub, map_mul]
  ring

theorem generalMatchingDiscPolynomial_scaled (m : ℕ) (a : Fin p) :
    (Li2.matchingDiscProduct p a.val m).map (Rat.castHom ℚ_[p]) =
      C ((p : ℚ_[p]) ^ matchingCount m p a) *
        (generalMatchingDiscPolynomial m a).map (algebraMap ℤ_[p] ℚ_[p]) := by
  classical
  let s := (Finset.Icc 1 m).filter (fun j => j % p = a.val)
  have hfac : ∀ j ∈ s,
      (C (p : ℚ_[p]) * X + C ((j : ℚ_[p]) - (a.val : ℚ_[p])) : (ℚ_[p])[X]) =
        C (p : ℚ_[p]) * (X + C ((j / p : ℕ) : ℚ_[p])) := by
    intro j hj
    exact generalMatchingDiscFactor_scaled j a (Finset.mem_filter.mp hj).2
  simp only [Li2.matchingDiscProduct, generalMatchingDiscPolynomial,
    matchingCount, Polynomial.map_prod, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Rat.coe_castHom, map_natCast]
  simp only [Polynomial.map_natCast, Rat.cast_natCast, Rat.cast_sub]
  change (∏ j ∈ s,
      (C (p : ℚ_[p]) * X + C ((j : ℚ_[p]) - (a.val : ℚ_[p])) : (ℚ_[p])[X])) =
    C ((p : ℚ_[p]) ^ s.card) *
      ∏ j ∈ s, (X + C ((j / p : ℕ) : ℚ_[p]))
  calc
    _ = ∏ j ∈ s, C (p : ℚ_[p]) *
        (X + C ((j / p : ℕ) : ℚ_[p])) :=
      Finset.prod_congr rfl hfac
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp

#print axioms generalMatchingDiscPolynomial_split
#print axioms generalMatchingDiscFactor_scaled
#print axioms generalMatchingDiscPolynomial_scaled

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalNonmatchingQuotient (n : ℕ) (a : Fin p) : PowerSeries ℤ_[p] :=
  (Li2.integralNonmatchingDiscPolynomial (p := p) a.val n : PowerSeries ℤ_[p]) ^ 3 *
    Li2.nonmatchingDiscInverse (p := p) a.val (4 * n) a.isLt

def generalNonmatchingConstant (n : ℕ) (a : Fin p) : ℤ_[p] :=
  Li2.nonmatchingDiscConstant (p := p) a.val n ^ 3 *
    Li2.nonmatchingInverseConstant (p := p) a.val (4 * n) a.isLt

theorem generalNonmatchingQuotient_restricted (n : ℕ) (a : Fin p) :
    PowerSeries.IsRestricted 1 (generalNonmatchingQuotient n a) := by
  exact PowerSeries.IsRestricted.mul 1
    (Li2.restricted_pow _ (Li2.polynomial_isRestricted _) 3)
    (Li2.nonmatchingDiscInverse_isRestricted a.val (4 * n) a.isLt)

theorem generalNonmatchingQuotient_cleared (n : ℕ) (a : Fin p) :
    generalNonmatchingQuotient n a *
      (Li2.integralNonmatchingDiscPolynomial (p := p) a.val (4 * n) : PowerSeries ℤ_[p]) =
      (Li2.integralNonmatchingDiscPolynomial (p := p) a.val n : PowerSeries ℤ_[p]) ^ 3 := by
  unfold generalNonmatchingQuotient
  rw [mul_assoc, Li2.nonmatchingDiscInverse_identity, mul_one]

theorem generalNonmatchingQuotient_constant_error (n : ℕ) (a : Fin p) (k : ℕ) :
    ‖PowerSeries.coeff k
      (generalNonmatchingQuotient n a -
        PowerSeries.C (generalNonmatchingConstant n a))‖ ≤ ‖(p : ℤ_[p])‖ := by
  apply Li2.powerSeries_mul_constant_error_bound _ _ _ _ _ (norm_nonneg _)
  · exact Li2.powerSeries_pow_constant_error_bound _ _ _ (norm_nonneg _)
      (Li2.nonmatchingDiscPolynomial_constant_error a.val n) 3
  · exact Li2.nonmatchingDiscInverse_constant_error a.val (4 * n) a.isLt

#print axioms generalNonmatchingQuotient_cleared
#print axioms generalNonmatchingQuotient_constant_error

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem general_tail_integral_cleared (n : ℕ) (a : Fin p)
    (hp : 0 < p) (hsq : 4 * n < p * p) :
    ∃ g : PowerSeries ℤ_[p], ∃ r : Fin p → ℤ_[p],
      PowerSeries.IsRestricted 1 g ∧
      (generalMatchingTailPolynomial n a : PowerSeries ℤ_[p]) *
        integralPoleNumerator (generalPoleCenters (p := p)) g r =
      (integralPoleDenominator (generalPoleCenters (p := p)) : PowerSeries ℤ_[p]) *
        (generalMatchingDiscPolynomial n a : PowerSeries ℤ_[p]) ^ 2 *
          generalNonmatchingQuotient n a := by
  classical
  let s := generalTailPoleSet n p a
  let M := generalMatchingDiscPolynomial n a
  obtain ⟨g₀, r₀, h₀⟩ := generalPoleSubset_integral_cleared s (M ^ 2)
  refine ⟨integralPoleMulRegular (generalPoleCenters (p := p))
      (generalNonmatchingQuotient n a) (g₀ : PowerSeries ℤ_[p]) r₀,
    integralPoleMulResidue (generalPoleCenters (p := p))
      (generalNonmatchingQuotient n a) r₀, ?_, ?_⟩
  · exact integralPoleMulRegular_isRestricted _ _ _
      (generalNonmatchingQuotient_restricted n a)
      (polynomial_isRestricted _) _
  · rw [generalMatchingTailPolynomial_subset n a hp hsq]
    rw [integralPoleNumerator_mul _ _ _
      (generalNonmatchingQuotient_restricted n a)]
    simpa only [Polynomial.coe_pow, s, M] using
      (show (generalPoleSubsetDenominator s : PowerSeries ℤ_[p]) *
          (generalNonmatchingQuotient n a *
            integralPoleNumerator (generalPoleCenters (p := p))
              (g₀ : PowerSeries ℤ_[p]) r₀) =
          (integralPoleDenominator (generalPoleCenters (p := p)) :
            PowerSeries ℤ_[p]) *
              (M : PowerSeries ℤ_[p]) ^ 2 *
                generalNonmatchingQuotient n a from by
        rw [mul_left_comm, h₀, Polynomial.coe_pow]
        ring)

#print axioms general_tail_integral_cleared

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem general_disc_factorization (m : ℕ) (a : Fin p) :
    primeDiscPolynomialSeries a.val m =
      PowerSeries.C ((p : ℚ_[p]) ^ matchingCount m p a) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (generalMatchingDiscPolynomial m a : PowerSeries ℤ_[p]) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (integralNonmatchingDiscPolynomial (p := p) a.val m : PowerSeries ℤ_[p]) := by
  classical
  have hm := congrArg (fun Q : (ℚ_[p])[X] => (Q : PowerSeries ℚ_[p]))
    (generalMatchingDiscPolynomial_scaled m a)
  have hm' : rationalPolynomialSeries (p := p) (matchingDiscProduct p a.val m) =
      PowerSeries.C ((p : ℚ_[p]) ^ matchingCount m p a) *
        PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
          (generalMatchingDiscPolynomial m a : PowerSeries ℤ_[p]) := by
    change (((matchingDiscProduct p a.val m).map (Rat.castHom ℚ_[p]) :
      (ℚ_[p])[X]) : PowerSeries ℚ_[p]) = _
    simpa only [Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.polynomial_map_coe] using hm
  rw [primeDiscPolynomialSeries_factorization, hm',
    nonmatchingDiscPolynomialSeries_eq]

#print axioms general_disc_factorization

end
end Li2Unified.Proofs.Hermite

end


end
