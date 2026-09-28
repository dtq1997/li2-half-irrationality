module
public import Li2Unified.Modular.Base.RestrictedPolynomialTranslation
public import Li2Unified.Modular.Base.RestrictedInverseDerivative

set_option backward.privateInPublic true

@[expose] public section

/-! Restricted inverses of affine unit factors, and their translated rational
identity. The constant coefficient is an actual unit, not an unproved inverse. -/
open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def affineInverseSeries (a : ℤ_[p]ˣ) (b : ℤ_[p]) (d : ℕ) : PowerSeries ℤ_[p] :=
  PowerSeries.C ((↑a⁻¹:ℤ_[p])^d)*inverseOneSubSeries (-b*(↑a⁻¹:ℤ_[p])) d

lemma affineInverseSeries_isRestricted (a : ℤ_[p]ˣ) (b : ℤ_[p]) (hb : ‖b‖ < 1) (d : ℕ) :
    PowerSeries.IsRestricted 1 (affineInverseSeries a b d) := by
  apply PowerSeries.IsRestricted.mul 1 (PowerSeries.IsRestricted.C 1 _)
  apply inverseOneSubSeries_isRestricted
  apply lt_of_le_of_lt (integral_coeff_mul_norm_le _ _) (by simpa only [norm_neg] using hb)

theorem affineInverseSeries_identity (a : ℤ_[p]ˣ) (b : ℤ_[p]) (d : ℕ) :
    affineInverseSeries a b d*(PowerSeries.C (a:ℤ_[p])+PowerSeries.C b*PowerSeries.X)^d = 1 := by
  have hu : PowerSeries.C (a:ℤ_[p])*PowerSeries.C (↑a⁻¹:ℤ_[p]) = 1 := by
    rw [← map_mul]
    simp
  have hd : PowerSeries.C (a:ℤ_[p])+PowerSeries.C b*PowerSeries.X =
      PowerSeries.C (a:ℤ_[p])*(1-PowerSeries.C (-b*(↑a⁻¹:ℤ_[p]))*PowerSeries.X) := by
    simp only [map_mul, map_neg]
    calc
      _ = PowerSeries.C (a:ℤ_[p]) +
          (PowerSeries.C (a:ℤ_[p])*PowerSeries.C (↑a⁻¹:ℤ_[p]))*PowerSeries.C b*PowerSeries.X := by rw [hu]; ring
      _ = _ := by ring
  have hc : PowerSeries.C ((↑a⁻¹:ℤ_[p])^d)*PowerSeries.C (a:ℤ_[p])^d = 1 := by
    rw [map_pow, ← mul_pow, mul_comm _ (PowerSeries.C (a:ℤ_[p])), hu, one_pow]
  rw [hd, mul_pow]
  unfold affineInverseSeries
  calc
    _ = (PowerSeries.C ((↑a⁻¹:ℤ_[p])^d)*PowerSeries.C (a:ℤ_[p])^d)*
        (inverseOneSubSeries (-b*(↑a⁻¹:ℤ_[p])) d*
          (1-PowerSeries.C (-b*(↑a⁻¹:ℤ_[p]))*PowerSeries.X)^d) := by ring
    _ = 1 := by rw [hc, inverseOneSubSeries_identity, one_mul]

theorem affineInverseSeries_eval (a : ℤ_[p]ˣ) (b : ℤ_[p]) (hb : ‖b‖ < 1)
    (d : ℕ) (x : ℤ_[p]) :
    restrictedEval x (affineInverseSeries a b d)*((a:ℤ_[p])+b*x)^d = 1 := by
  have hpoly : (((C (a:ℤ_[p])+C b*X)^d : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) =
      (PowerSeries.C (a:ℤ_[p])+PowerSeries.C b*PowerSeries.X)^d := by simp
  have h := congrArg (restrictedEval x) (affineInverseSeries_identity a b d)
  rw [← hpoly, restrictedEval_mul _ _ _ (affineInverseSeries_isRestricted a b hb d)
    (polynomial_isRestricted _), restrictedEval_polynomial, restrictedEval_one] at h
  simpa using h

theorem affineInverseSeries_translate_identity (a : ℤ_[p]ˣ) (b : ℤ_[p])
    (hb : ‖b‖ < 1) (d : ℕ) (c : ℤ_[p]) :
    (PowerSeries.C ((a:ℤ_[p])+b*c)+PowerSeries.C b*PowerSeries.X)^d*
      restrictedTranslate c (affineInverseSeries a b d) = 1 := by
  have hpoly : (((C (a:ℤ_[p])+C b*X)^d : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) =
      (PowerSeries.C (a:ℤ_[p])+PowerSeries.C b*PowerSeries.X)^d := by simp
  have hid : (((C (a:ℤ_[p])+C b*X)^d : (ℤ_[p])[X]) : PowerSeries ℤ_[p])*
      affineInverseSeries a b d = 1 := by
    rw [hpoly, mul_comm, affineInverseSeries_identity]
  have ht := congrArg (restrictedTranslate c) hid
  rw [restrictedTranslate_polynomial_mul _ _ _ (affineInverseSeries_isRestricted a b hb d)] at ht
  have h1 : restrictedTranslate c (1 : PowerSeries ℤ_[p]) = 1 := by
    simpa using restrictedTranslate_polynomial c (1 : (ℤ_[p])[X])
  rw [h1] at ht
  have he : (((((C (a:ℤ_[p])+C b*X)^d).comp (X+C c) : (ℤ_[p])[X])) : PowerSeries ℤ_[p]) =
      (PowerSeries.C ((a:ℤ_[p])+b*c)+PowerSeries.C b*PowerSeries.X)^d := by
    simp only [pow_comp, add_comp, C_comp, mul_comp, X_comp,
      Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X, map_add, map_mul]
    congr 1
    ring
  rw [he] at ht
  exact ht

end
end Li2

end
