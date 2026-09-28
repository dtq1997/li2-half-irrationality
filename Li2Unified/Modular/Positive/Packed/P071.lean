module
public import Li2Unified.Modular.Positive.Packed.P070
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.OriginalRealDerivative

set_option backward.privateInPublic true

@[expose] public section

section
/-! Actual quotient derivative series, preserving the old parameter-free
quotient and its independently proved derivative formula. No contour equality. -/
open Polynomial
open scoped BigOperators
namespace Li2Unified.ParameterFamily
noncomputable section

lemma polynomialIntegrand_cast (F : ℚ[X]) (x : ℚ) :
    (((X*F).derivative.eval x : ℚ) : ℝ) = Li2.polynomialIntegrand F (x:ℝ) := by
  have he : (((X*F).derivative.eval x : ℚ) : ℝ) =
      ((X*F).map (Rat.castHom ℝ)).derivative.eval (x:ℝ) := by
    rw [derivative_map, eval_map]
    exact (eval₂_at_apply (p := (X*F).derivative) (Rat.castHom ℝ) x).symm
  rw [he, Li2.polynomialIntegrand_derivative, Polynomial.map_mul, Polynomial.map_X,
    mul_comm (X:ℝ[X])]

lemma parameterU_series_term (lam : ℚ) (F : ℚ[X]) (k : ℕ) :
    ((lam^(k+1)*(X*F).derivative.eval ((k:ℚ)+1) : ℚ) : ℝ) =
      (lam:ℝ)^(k+1)*Li2.polynomialIntegrand F ((k:ℝ)+1) := by
  simp only [Rat.cast_mul, Rat.cast_pow, polynomialIntegrand_cast,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_one]

lemma summable_parameterU (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (F : ℚ[X]) :
    Summable (fun k : ℕ => (lam:ℝ)^(k+1)*Li2.polynomialIntegrand F ((k:ℝ)+1)) := by
  have h := Li2.summable_parameterPolynomial lam (by simpa only [Real.norm_eq_abs] using hlam)
    (X*F).derivative
  simpa only [parameterU_series_term] using h

lemma parameterU_real_series (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (F : ℚ[X]) :
    (Li2.parameterU lam F : ℝ) =
      ∑' k : ℕ, (lam:ℝ)^(k+1)*Li2.polynomialIntegrand F ((k:ℝ)+1) := by
  unfold Li2.parameterU
  rw [Li2.parameterG_cast_eq_series lam (by simpa only [Real.norm_eq_abs] using hlam)]
  simp only [parameterU_series_term]

def poleDerivativeTerm (lam : ℚ) (j k : ℕ) : ℝ :=
  (lam:ℝ)^(k+1) * (j:ℝ) / ((k+j:ℕ)+1:ℝ)^2

lemma summable_poleDerivativeTerm (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (j : ℕ) :
    Summable (poleDerivativeTerm lam j) := by
  have hg : Summable (fun k : ℕ => |(lam:ℝ)|^(k+1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (abs_nonneg (lam:ℝ)) hlam).mul_right |(lam:ℝ)|
  have hb : Summable (fun k : ℕ => |(lam:ℝ)^(k+1) / ((k+j:ℕ)+1:ℝ)^2|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ hg
    intro k
    rw [abs_div, abs_pow, abs_pow,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k+j:ℕ)+1:ℝ))]
    have hk : (0:ℝ) ≤ (k+j:ℕ) := Nat.cast_nonneg _
    have hd : (1:ℝ) ≤ ((k+j:ℕ)+1:ℝ)^2 := by nlinarith
    exact div_le_self (by positivity) hd
  have h := (summable_abs_iff.mp hb).mul_right (j:ℝ)
  convert h using 1
  funext k
  unfold poleDerivativeTerm
  ring

lemma realDerivativeExpansion_term (lam : ℚ) (m : ℕ) (F : ℚ[X]) (k : ℕ) :
    (lam:ℝ)^(k+1)*Li2.originalRealDerivativeExpansion m F ((k:ℝ)+1) =
      (lam:ℝ)^(k+1)*Li2.polynomialIntegrand (F /ₘ Li2.D m) ((k:ℝ)+1) +
      ∑ j ∈ Finset.Icc 1 m, (Li2.originalResidue m F j:ℝ)*poleDerivativeTerm lam j k := by
  unfold Li2.originalRealDerivativeExpansion
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold poleDerivativeTerm
  push_cast
  ring

theorem summable_realDerivativeExpansion (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (m : ℕ) (F : ℚ[X]) :
    Summable (fun k : ℕ => (lam:ℝ)^(k+1)*Li2.originalRealDerivativeExpansion m F ((k:ℝ)+1)) := by
  simp_rw [realDerivativeExpansion_term]
  apply (summable_parameterU lam hlam (F /ₘ Li2.D m)).add
  apply summable_sum
  intro j _
  exact (summable_poleDerivativeTerm lam hlam j).mul_left _

theorem numeratorFunctional_real_series (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (h0 : lam ≠ 0)
    (m : ℕ) (F : ℚ[X]) :
    (numeratorFunctional lam m F).eval₂ (Rat.castHom ℝ) (r lam) =
      ∑' k : ℕ, (lam:ℝ)^(k+1)*Li2.originalRealDerivativeExpansion m F ((k:ℝ)+1) := by
  have hp := summable_parameterU lam hlam (F /ₘ Li2.D m)
  have hs (j : ℕ) : Summable (fun k : ℕ =>
      (Li2.originalResidue m F j:ℝ)*poleDerivativeTerm lam j k) :=
    (summable_poleDerivativeTerm lam hlam j).mul_left _
  have hsum : Summable (fun k : ℕ => ∑ j ∈ Finset.Icc 1 m,
      (Li2.originalResidue m F j:ℝ)*poleDerivativeTerm lam j k) := by
    apply summable_sum
    intro j _
    exact hs j
  simp_rw [realDerivativeExpansion_term]
  rw [hp.tsum_add hsum, Summable.tsum_finsetSum]
  · rw [← parameterU_real_series lam hlam]
    simp_rw [tsum_mul_left, poleDerivativeTerm, pole_functional_identity lam hlam h0]
    simp only [numeratorFunctional, Li2.originalResidue, eval₂_add, eval₂_C,
      eval₂_finset_sum, eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom,
      Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_inv]
  · intro j _
    exact hs j

theorem numeratorFunctional_real_derivative_series
    (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (h0 : lam ≠ 0) (m : ℕ) (F : ℚ[X]) :
    (numeratorFunctional lam m F).eval₂ (Rat.castHom ℝ) (r lam) =
      ∑' k : ℕ, (lam:ℝ)^(k+1)*
        deriv (fun x : ℝ => x*Li2.originalRealQuotient m F x) ((k:ℝ)+1) := by
  rw [numeratorFunctional_real_series lam hlam h0]
  apply tsum_congr
  intro k
  rw [(Li2.originalRealQuotient_hasDerivAt m F (x := (k:ℝ)+1) (by positivity)).deriv]

theorem summable_originalRealQuotient_derivative
    (lam : ℚ) (hlam : |(lam:ℝ)| < 1) (m : ℕ) (F : ℚ[X]) :
    Summable (fun k : ℕ => (lam:ℝ)^(k+1)*
      deriv (fun x : ℝ => x*Li2.originalRealQuotient m F x) ((k:ℝ)+1)) := by
  apply (summable_realDerivativeExpansion lam hlam m F).congr
  intro k
  rw [(Li2.originalRealQuotient_hasDerivAt m F (x := (k:ℝ)+1) (by positivity)).deriv]

theorem Q_real_derivative_series_det (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (h0 : lam ≠ 0) (n : ℕ) :
    (Q lam n).eval₂ (Rat.castHom ℝ) (r lam) =
      (Matrix.of fun i j : Fin (2*n) =>
        ∑' k : ℕ, (lam:ℝ)^(k+1) *
          deriv (fun x : ℝ => x*Li2.originalRealQuotient (4*n)
            (Li2.numerator n (i.val+j.val)) x) ((k:ℝ)+1)).det := by
  change (eval₂RingHom (Rat.castHom ℝ) (r lam)) (Q lam n) = _
  rw [Q, ← hankelFor_original lam n, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change (numeratorFunctional lam (4*n) ((Li2.D n)^3*X^(i.val+j.val))).eval₂
    (Rat.castHom ℝ) (r lam) = _
  rw [mul_comm ((Li2.D n)^3)]
  exact numeratorFunctional_real_derivative_series lam hlam h0 (4*n)
    (Li2.numerator n (i.val+j.val))

end
end Li2Unified.ParameterFamily

end


end
