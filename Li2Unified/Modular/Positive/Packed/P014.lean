module
public import Li2Unified.Modular.Positive.Packed.P013
public import Li2Unified.Modular.Base.PrimeFieldPoleExtension
public import Li2Unified.Modular.Base.RationalBaseEvaluation
public import Li2Unified.Modular.Positive.Packed.P010

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterUPole_eval₂ (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (j : ℕ) (hj : j < p) (Y : ℚ_[p]) :
    (integralUPole z hz hv j hj).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      (j:ℚ_[p])*(z:ℚ_[p])⁻¹^j*(Y-(parameterTau z j:ℚ_[p])) := by
  unfold integralUPole
  rw [eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_C]
  simp only [map_mul, map_neg, map_natCast, PadicInt.algebraMap_apply]
  simp [integralParameterInvPow, integralParameterTau, integralRational]

theorem parameterVPole_eval₂ (z : ℚ) (hz : z ≠ 0) (hv : padicValRat p z = 0)
    (j : ℕ) (hj : j < p) (Y : ℚ_[p]) :
    (integralVPole z hz hv j hj).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      -(z:ℚ_[p])⁻¹^j*(Y-(parameterTau z j:ℚ_[p])) := by
  unfold integralVPole
  rw [eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_C]
  simp only [map_mul, map_neg, map_natCast, PadicInt.algebraMap_apply]
  simp [integralParameterInvPow, integralParameterTau, integralRational]

def fieldParameterFourPoleU (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) (r : Fin 4 → ℚ_[p]) : (ℚ_[p])[X] :=
  fieldPoleFunctional
    (fun n => (n+1:ℕ)*integralParameterMoment z hreg n)
    (fun j : Fin 4 => (integralUPole z hu.1 hu.2 j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p])) f r

def fieldParameterFourPoleV (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) (r : Fin 4 → ℚ_[p]) : (ℚ_[p])[X] :=
  fieldPoleFunctional
    (derivativeMoments (integralParameterMoment z hreg))
    (fun j : Fin 4 => (integralVPole z hu.1 hu.2 j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p])) f r

theorem fieldParameterFourPoleU_integral (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : Fin 4 → ℤ_[p]) :
    fieldParameterFourPoleU z hu hreg hp4 (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i:ℚ_[p])) =
      (parameterFourPoleU z hu hreg hp4 f r).map (algebraMap ℤ_[p] ℚ_[p]) :=
  fieldPoleFunctional_integral _ _ f hf r

theorem fieldParameterFourPoleV_integral (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (r : Fin 4 → ℤ_[p]) :
    fieldParameterFourPoleV z hu hreg hp4 (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i:ℚ_[p])) =
      (parameterFourPoleV z hu hreg hp4 f r).map (algebraMap ℤ_[p] ℚ_[p]) :=
  fieldPoleFunctional_integral _ _ f hf r

lemma fieldParameterFourPoleU_regular (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) :
    fieldParameterFourPoleU z hu hreg hp4 f 0 = C (fieldRestrictedU
      (integralParameterMoment z hreg) f) := by
  simp [fieldParameterFourPoleU, fieldPoleFunctional, fieldRestrictedU]

lemma fieldParameterFourPoleV_regular (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : PowerSeries ℚ_[p]) :
    fieldParameterFourPoleV z hu hreg hp4 f 0 = C (fieldRestrictedV
      (integralParameterMoment z hreg) f) := by
  simp [fieldParameterFourPoleV, fieldPoleFunctional, fieldRestrictedV]

theorem fieldParameterFourPoleU_polynomial (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (P : ℚ[X]) (Y : ℚ_[p]) :
    (fieldParameterFourPoleU z hu hreg hp4 (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) 0).eval Y =
      (parameterU z P : ℚ_[p]) := by
  rw [fieldParameterFourPoleU_regular, eval_C, fieldParameterU_polynomial]

theorem fieldParameterFourPoleV_polynomial (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (P : ℚ[X]) (Y : ℚ_[p]) :
    (fieldParameterFourPoleV z hu hreg hp4 (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) 0).eval Y =
      (parameterV z P : ℚ_[p]) := by
  rw [fieldParameterFourPoleV_regular, eval_C, fieldParameterV_polynomial]

theorem fieldParameterFourPoleU_single (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (j : Fin 4) (r : ℚ_[p]) :
    fieldParameterFourPoleU z hu hreg hp4 0 (Pi.single j r) =
      C r * (integralUPole z hu.1 hu.2 j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [fieldParameterFourPoleU, fieldPoleFunctional, fieldRestrictedMoment, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem fieldParameterFourPoleV_single (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (j : Fin 4) (r : ℚ_[p]) :
    fieldParameterFourPoleV z hu hreg hp4 0 (Pi.single j r) =
      C r * (integralVPole z hu.1 hu.2 j.val (by omega)).map (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [fieldParameterFourPoleV, fieldPoleFunctional, fieldRestrictedMoment, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem fieldParameterFourPoleU_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : ℚ[X])
    (r : Fin 4 → ℚ) (Y : ℚ_[p]) :
    (fieldParameterFourPoleU z hu hreg hp4 (f.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p])
      (fun j => (r j : ℚ_[p]))).eval Y =
    (rationalPoleU z f r).eval₂ (Rat.castHom ℚ_[p]) Y := by
  change (C (fieldRestrictedU _ _) + ∑ j : Fin 4,
    C (r j : ℚ_[p]) * (integralUPole z hu.1 hu.2 j.val (by omega)).map
      (algebraMap ℤ_[p] ℚ_[p])).eval Y = _
  rw [fieldParameterU_polynomial]
  simp only [rationalPoleU, eval_add, eval_C, eval_finset_sum, eval_mul,
    eval_map, parameterUPole_eval₂, eval₂_add, eval₂_C, eval₂_finset_sum,
    eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fieldParameterFourPoleV_rational (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hreg : VG p (z/(1-z)) 0) (hp4 : 3 < p) (f : ℚ[X])
    (r : Fin 4 → ℚ) (Y : ℚ_[p]) :
    (fieldParameterFourPoleV z hu hreg hp4 (f.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p])
      (fun j => (r j : ℚ_[p]))).eval Y =
    (rationalPoleV z f r).eval₂ (Rat.castHom ℚ_[p]) Y := by
  change (C (fieldRestrictedV _ _) + ∑ j : Fin 4,
    C (r j : ℚ_[p]) * (integralVPole z hu.1 hu.2 j.val (by omega)).map
      (algebraMap ℤ_[p] ℚ_[p])).eval Y = _
  rw [fieldParameterV_polynomial]
  simp only [rationalPoleV, eval_add, eval_C, eval_finset_sum, eval_mul,
    eval_map, parameterVPole_eval₂, eval₂_add, eval₂_C, eval₂_finset_sum,
    eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_inv, Rat.cast_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.fieldParameterFourPoleU_rational
#print axioms Li2Unified.Proofs.PrimeEdge.fieldParameterFourPoleV_rational

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def generalFieldPoleU (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℚ_[p]) (r : Fin p → ℚ_[p]) : (ℚ_[p])[X] :=
  fieldPoleFunctional
    (fun n => (n + 1 : ℕ) * integralParameterMoment z hz n)
    (fun k : Fin p =>
      (integralUPole z hu.1 hu.2 k.val k.isLt).map (algebraMap ℤ_[p] ℚ_[p])) f r

def generalFieldPoleV (z : ℚ) (hu : z ≠ 0 ∧ padicValRat p z = 0)
    (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℚ_[p]) (r : Fin p → ℚ_[p]) : (ℚ_[p])[X] :=
  fieldPoleFunctional
    (derivativeMoments (integralParameterMoment z hz))
    (fun k : Fin p =>
      (integralVPole z hu.1 hu.2 k.val k.isLt).map (algebraMap ℤ_[p] ℚ_[p])) f r

theorem generalFieldPoleU_integral (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin p → ℤ_[p]) :
    generalFieldPoleU z hu hz
      (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i : ℚ_[p])) =
      (generalPoleU z hu hz f r).map (algebraMap ℤ_[p] ℚ_[p]) := by
  exact fieldPoleFunctional_integral _ _ f hf r

theorem generalFieldPoleV_integral (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hz : VG p (z / (1 - z)) 0)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (r : Fin p → ℤ_[p]) :
    generalFieldPoleV z hu hz
      (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) (fun i => (r i : ℚ_[p])) =
      (generalPoleV z hu hz f r).map (algebraMap ℤ_[p] ℚ_[p]) := by
  exact fieldPoleFunctional_integral _ _ f hf r

theorem generalFieldPoleU_polynomial (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hz : VG p (z / (1 - z)) 0)
    (P : ℚ[X]) (Y : ℚ_[p]) :
    (generalFieldPoleU z hu hz (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) 0).eval Y =
      (parameterU z P : ℚ_[p]) := by
  simpa [generalFieldPoleU, fieldPoleFunctional, fieldRestrictedU] using
    (fieldParameterU_polynomial z hz P)

theorem generalFieldPoleV_polynomial (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hz : VG p (z / (1 - z)) 0)
    (P : ℚ[X]) (Y : ℚ_[p]) :
    (generalFieldPoleV z hu hz (P.map (Rat.castHom ℚ_[p]) : PowerSeries ℚ_[p]) 0).eval Y =
      (parameterV z P : ℚ_[p]) := by
  simpa [generalFieldPoleV, fieldPoleFunctional, fieldRestrictedV] using
    (fieldParameterV_polynomial z hz P)

theorem generalFieldPoleU_single (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hz : VG p (z / (1 - z)) 0)
    (k : Fin p) (r : ℚ_[p]) :
    generalFieldPoleU z hu hz 0 (Pi.single k r) =
      C r * (integralUPole z hu.1 hu.2 k.val k.isLt).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [generalFieldPoleU, fieldPoleFunctional, fieldRestrictedMoment, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem generalFieldPoleV_single (z : ℚ)
    (hu : z ≠ 0 ∧ padicValRat p z = 0) (hz : VG p (z / (1 - z)) 0)
    (k : Fin p) (r : ℚ_[p]) :
    generalFieldPoleV z hu hz 0 (Pi.single k r) =
      C r * (integralVPole z hu.1 hu.2 k.val k.isLt).map
        (algebraMap ℤ_[p] ℚ_[p]) := by
  simp [generalFieldPoleV, fieldPoleFunctional, fieldRestrictedMoment, Pi.single_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

#print axioms generalFieldPoleU_integral
#print axioms generalFieldPoleV_integral
#print axioms generalFieldPoleU_polynomial
#print axioms generalFieldPoleV_polynomial
#print axioms generalFieldPoleU_single
#print axioms generalFieldPoleV_single

end
end Li2Unified.Proofs.Hermite

end


end
