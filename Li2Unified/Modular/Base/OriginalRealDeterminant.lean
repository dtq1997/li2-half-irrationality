module
public import Li2Unified.Modular.Base.OriginalRealDerivative
public import Li2Unified.Modular.Base.Gram

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section

theorem Q_real_derivative_series_det (n : ℕ) :
    (Q n).eval₂ (Rat.castHom ℝ) li2NegHalf =
      (Matrix.of fun i j : Fin (2*n) =>
        ∑' k : ℕ, (-1/2:ℝ)^(k+1) *
          deriv (fun x : ℝ => x*originalRealQuotient (4*n)
            (numerator n (i.val+j.val)) x) ((k:ℝ)+1)).det := by
  change (eval₂RingHom (Rat.castHom ℝ) li2NegHalf) (Q n) = _
  rw [Q, ← hankelFor_original, RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  change (numeratorFunctional (4*n) ((D n)^3*X^(i.val+j.val))).eval₂
    (Rat.castHom ℝ) li2NegHalf = _
  rw [mul_comm ((D n)^3)]
  exact numeratorFunctional_real_derivative_series (4*n)
    (numerator n (i.val+j.val))

end
end Li2

end
