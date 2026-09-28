module
public import Li2Unified.Modular.Positive.Packed.P169

set_option backward.privateInPublic true

@[expose] public section

section
/-! Soundness of the nonlinear atom constructors, using the already proved
real-analysis bounds. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf

open Li2Unified.ParameterFamily

theorem qValid_qPow2Z (k : ℤ) : qValid (qPow2Z k) = true := by
  unfold qPow2Z
  split_ifs
  · simp [qValid]
  · simp [qValid]

theorem qPow2Z_toRat (k : ℤ) : (qPow2Z k).toRat = (2 : ℚ) ^ k := by
  by_cases hk : 0 ≤ k
  · have hkn : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    rw [qPow2Z, if_pos hk]
    simp only [QPair.toRat, Nat.cast_one, div_one]
    conv_rhs => rw [← hkn, zpow_natCast]
    norm_cast
  · have hneg : 0 ≤ -k := le_of_lt (neg_pos.mpr (lt_of_not_ge hk))
    have hkn : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg hneg
    rw [qPow2Z, if_neg hk]
    change (1 : ℚ) / ((2 ^ (-k).toNat : ℕ) : ℚ) = (2 : ℚ) ^ k
    have hk' : k = -((-k).toNat : ℤ) := by omega
    conv_rhs => rw [hk', zpow_neg, zpow_natCast]
    simp

theorem logAtom_ratio_sound {q u rho : QPair} {k : ℤ}
    (hq : qValid q = true) (hu : qValid u = true)
    (_hrho : qValid rho = true) (hrho0 : qLT qZero rho = true)
    (heq : qEq q (qDiv (qMul (qPow2Z k) u) rho) = true) :
    q.toRat = (2 : ℚ) ^ k * u.toRat / rho.toRat := by
  have hval : qValid (qDiv (qMul (qPow2Z k) u) rho) = true :=
    qValid_qDiv_pos (qValid_qMul (qValid_qPow2Z k) hu) hrho0
  have h := qEq_sound hq hval heq
  rw [toRat_qDiv_pos _ _ hrho0, toRat_qMul, qPow2Z_toRat] at h
  exact h

private def EndpointsValid (a : I) : Prop :=
  qValid a.lo = true ∧ qValid a.hi = true

private theorem endpointsValid_point (q : QPair) (hq : qValid q = true) :
    EndpointsValid (point q) := ⟨hq, hq⟩

private theorem endpointsValid_add {a b : I}
    (ha : EndpointsValid a) (hb : EndpointsValid b) :
    EndpointsValid (add a b) := by
  exact ⟨qValid_qAdd ha.1 hb.1, qValid_qAdd ha.2 hb.2⟩

private theorem endpointsValid_neg {a : I} (ha : EndpointsValid a) :
    EndpointsValid (neg a) := by
  exact ⟨qValid_qNeg ha.2, qValid_qNeg ha.1⟩

private theorem endpointsValid_mul {a b : I}
    (ha : EndpointsValid a) (hb : EndpointsValid b) :
    EndpointsValid (mul a b) := by
  have hll := qValid_qMul ha.1 hb.1
  have hlu := qValid_qMul ha.1 hb.2
  have hul := qValid_qMul ha.2 hb.1
  have huu := qValid_qMul ha.2 hb.2
  exact ⟨qValid_qMin (qValid_qMin hll hlu) (qValid_qMin hul huu),
    qValid_qMax (qValid_qMax hll hlu) (qValid_qMax hul huu)⟩

private theorem toBounds_add_endpoints (a b : I)
    (ha : EndpointsValid a) (hb : EndpointsValid b) :
    (add a b).toBounds = RationalBounds.add a.toBounds b.toBounds := by
  exact congrArg₂ RationalBounds.mk
    (toRat_qAdd a.lo b.lo ha.1 hb.1)
    (toRat_qAdd a.hi b.hi ha.2 hb.2)

private theorem reducedLog_endpoints (r : QPair) (hr : qValid r = true)
    (hrpos : qLT qZero r = true) (n : ℕ) :
    EndpointsValid (reducedLogBounds r n) := by
  have hp := logPartial_valid r hr n
  have he := logError_valid r hr hrpos n
  exact ⟨qValid_qSub (qValid_qNeg hp) he,
    qValid_qAdd (qValid_qNeg hp) he⟩

private theorem validI_point (q : QPair) (hq : qValid q = true) :
    validI (point q) = true := by
  simp [validI, point, hq, qLE]

private theorem validI_logTwo : validI logTwoBounds = true := by decide

private theorem intPair_valid (k : ℤ) : qValid (⟨k, 1⟩ : QPair) = true := by
  simp [qValid]

theorem logTwoBounds_toBounds :
    logTwoBounds.toBounds = ParameterFamily.logTwoBounds := by
  norm_num [logTwoBounds, I.toBounds, QPair.toRat, ParameterFamily.logTwoBounds]

theorem piBounds_toBounds :
    piBounds.toBounds = ParameterFamily.piBounds := by
  norm_num [piBounds, I.toBounds, QPair.toRat, ParameterFamily.piBounds]

private theorem point_int_toBounds (k : ℤ) :
    (point ⟨k, 1⟩).toBounds = RationalBounds.point (k : ℚ) := by
  simp [point, I.toBounds, QPair.toRat, RationalBounds.point]

private theorem scaledLog_endpoints (k : ℤ) (u : QPair)
    (hu : qValid u = true) (hu0 : qLT qZero u = true) :
    EndpointsValid (scaledLogBounds k u) := by
  apply endpointsValid_add
  · exact endpointsValid_mul
      (endpointsValid_point ⟨k, 1⟩ (intPair_valid k))
      ⟨(validI_parts validI_logTwo).1, (validI_parts validI_logTwo).2.1⟩
  · exact reducedLog_endpoints u hu hu0 24

theorem scaledLogBounds_toBounds (k : ℤ) (u : QPair)
    (hu : qValid u = true) (hu0 : qLT qZero u = true) :
    (scaledLogBounds k u).toBounds =
      ParameterFamily.scaledLogBounds k u.toRat 24 := by
  change (add (mul (point ⟨k, 1⟩) logTwoBounds)
    (reducedLogBounds u 24)).toBounds = _
  rw [toBounds_add_endpoints _ _
    (endpointsValid_mul (endpointsValid_point ⟨k, 1⟩ (intPair_valid k))
      ⟨(validI_parts validI_logTwo).1, (validI_parts validI_logTwo).2.1⟩)
    (reducedLog_endpoints u hu hu0 24)]
  rw [toBounds_mul _ _ (validI_point ⟨k, 1⟩ (intPair_valid k)) validI_logTwo,
    point_int_toBounds, logTwoBounds_toBounds,
    reducedLogBounds_toBounds u hu hu0 24]
  rfl

theorem anchoredLogBounds_toBounds (k : ℤ) (u rho : QPair)
    (hu : qValid u = true) (hu0 : qLT qZero u = true)
    (hrho : qValid rho = true) (hrho0 : qLT qZero rho = true) :
    (anchoredLogBounds k u rho).toBounds =
      Li2Unified.Proofs.Potential.anchoredLogBounds k u.toRat rho.toRat := by
  change (add (scaledLogBounds k u) (neg (reducedLogBounds rho 2))).toBounds = _
  rw [toBounds_add_endpoints _ _ (scaledLog_endpoints k u hu hu0)
    (endpointsValid_neg (reducedLog_endpoints rho hrho hrho0 2))]
  rw [scaledLogBounds_toBounds k u hu hu0, toBounds_neg,
    reducedLogBounds_toBounds rho hrho hrho0 2]
  rfl

theorem contains_logAtom {q u rho : QPair} {k : ℤ}
    (hq : qValid q = true) (hu : qValid u = true)
    (hrho : qValid rho = true)
    (hu0 : qLT qZero u = true) (hu1 : qLE u qOne = true)
    (hrho0 : qLT qZero rho = true) (hrho1 : qLE rho qOne = true)
    (heq : qEq q (qDiv (qMul (qPow2Z k) u) rho) = true) :
    (anchoredLogBounds k u rho).toBounds.Contains (Real.log (q.toRat : ℝ)) := by
  rw [anchoredLogBounds_toBounds k u rho hu hu0 hrho hrho0]
  have hu0' : 0 < u.toRat := by
    simpa [qZero_toRat] using! qLT_sound qValid_qZero hu hu0
  have hu1' : u.toRat ≤ 1 := by
    simpa [qOne_toRat] using! qLE_sound hu qValid_qOne hu1
  have hrho0' : 0 < rho.toRat := by
    simpa [qZero_toRat] using! qLT_sound qValid_qZero hrho hrho0
  have hrho1' : rho.toRat ≤ 1 := by
    simpa [qOne_toRat] using! qLE_sound hrho qValid_qOne hrho1
  exact Li2Unified.Proofs.Potential.contains_anchored_log
    q.toRat u.toRat rho.toRat k hu0' hu1' hrho0' hrho1'
    (logAtom_ratio_sound hq hu hrho hrho0 heq)

#print axioms qPow2Z_toRat
#print axioms contains_logAtom

end Li2Unified.Proofs.Potential.KernelReflectionSelf

end

end
