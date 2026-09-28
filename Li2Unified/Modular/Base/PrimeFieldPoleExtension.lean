module
public import Li2Unified.Modular.Base.FieldPoleCompatibility
public import Li2Unified.Modular.Base.FieldParameterFunctional
public import Li2Unified.Modular.Base.PrimePoleFieldValues

set_option backward.privateInPublic true

@[expose] public section

/-! Extend the ACTUAL four-pole U/V functionals to Q_p coefficients.
The integral and rational-polynomial interfaces are proved explicitly. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def fieldPrimePoleU (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) (r : Fin 4 → ℚ_[p]) : (ℚ_[p])[X] :=
  fieldPoleFunctional
    (fun n => (n+1:ℕ)*integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral (by omega) (by omega)) n)
    (fun j : Fin 4 => (primeUPole (by omega) j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p])) f r

def fieldPrimePoleV (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) (r : Fin 4 → ℚ_[p]) : (ℚ_[p])[X] :=
  fieldPoleFunctional
    (derivativeMoments (integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral (by omega) (by omega))))
    (fun j : Fin 4 => (primeVPole (by omega) j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p])) f r

theorem fieldPrimePoleU_integral (hp4 : 3 < p) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : Fin 4 → ℤ_[p]) :
    fieldPrimePoleU hp4 (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i:ℚ_[p])) =
      (primePoleU hp4 f r).map (algebraMap ℤ_[p] ℚ_[p]) :=
  fieldPoleFunctional_integral _ _ f hf r

theorem fieldPrimePoleV_integral (hp4 : 3 < p) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : Fin 4 → ℤ_[p]) :
    fieldPrimePoleV hp4 (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i:ℚ_[p])) =
      (primePoleV hp4 f r).map (algebraMap ℤ_[p] ℚ_[p]) :=
  fieldPoleFunctional_integral _ _ f hf r

lemma fieldPrimePoleU_regular (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) :
    fieldPrimePoleU hp4 f 0 = C (fieldRestrictedU
      (integralParameterMoment (primeParameter p)
        (primeParameter_moment_integral (by omega) (by omega))) f) := by
  simp [fieldPrimePoleU, fieldPoleFunctional, fieldRestrictedU]

lemma fieldPrimePoleV_regular (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) :
    fieldPrimePoleV hp4 f 0 = C (fieldRestrictedV
      (integralParameterMoment (primeParameter p)
        (primeParameter_moment_integral (by omega) (by omega))) f) := by
  simp [fieldPrimePoleV, fieldPoleFunctional, fieldRestrictedV]

theorem fieldPrimePoleU_polynomial (hp4 : 3 < p) (P : ℚ[X]) (Y : ℚ_[p]) :
    (fieldPrimePoleU hp4 (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) 0).eval Y =
      (parameterU (primeParameter p) P : ℚ_[p]) := by
  rw [fieldPrimePoleU_regular, eval_C, fieldParameterU_polynomial]

theorem fieldPrimePoleV_polynomial (hp4 : 3 < p) (P : ℚ[X]) (Y : ℚ_[p]) :
    (fieldPrimePoleV hp4 (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) 0).eval Y =
      (parameterV (primeParameter p) P : ℚ_[p]) := by
  rw [fieldPrimePoleV_regular, eval_C, fieldParameterV_polynomial]

theorem fieldPrimePoleU_single (hp4 : 3 < p) (j : Fin 4) (r : ℚ_[p]) :
    fieldPrimePoleU hp4 0 (Pi.single j r) =
      C r * (primeUPole (by omega) j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [fieldPrimePoleU, fieldPoleFunctional, fieldRestrictedMoment, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem fieldPrimePoleV_single (hp4 : 3 < p) (j : Fin 4) (r : ℚ_[p]) :
    fieldPrimePoleV hp4 0 (Pi.single j r) =
      C r * (primeVPole (by omega) j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [fieldPrimePoleV, fieldPoleFunctional, fieldRestrictedMoment, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end
end Li2

end
