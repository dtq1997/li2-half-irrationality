module
public import Li2Unified.Modular.Positive.Packed.P170

set_option backward.privateInPublic true

@[expose] public section

section
/-! Arctangent atom soundness for the integer-pair checker. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf

open Li2Unified.ParameterFamily

theorem qLT_complete {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (h : a.toRat < b.toRat) : qLT a b = true := by
  have ha' : (0 : ℚ) < a.den := by exact_mod_cast qValid_pos ha
  have hb' : (0 : ℚ) < b.den := by exact_mod_cast qValid_pos hb
  have hc : (a.num : ℚ) * (b.den : ℚ) < (b.num : ℚ) * (a.den : ℚ) :=
    (div_lt_div_iff₀ ha' hb').mp h
  have hc' : a.num * Int.ofNat b.den < b.num * Int.ofNat a.den := by
    exact_mod_cast hc
  exact decide_eq_true hc'

theorem contains_atanSmall {q : QPair} {k : ℕ}
    (hq : qValid q = true) (hq0 : qLE qZero q = true)
    (hq1 : qLT q qOne = true) :
    (smallAtanBounds q k).toBounds.Contains (Real.arctan (q.toRat : ℝ)) := by
  rw [smallAtanBounds_toBounds q hq k]
  have h0 : 0 ≤ q.toRat := by
    simpa [qZero_toRat] using! qLE_sound qValid_qZero hq hq0
  have h1 : q.toRat < 1 := by
    simpa [qOne_toRat] using! qLT_sound hq qValid_qOne hq1
  exact contains_small_arctan q.toRat h0 h1 k

private theorem atanEnds (r : QPair) (hr : qValid r = true) (k : ℕ) :
    qValid (smallAtanBounds r k).lo = true ∧
    qValid (smallAtanBounds r k).hi = true := by
  exact ⟨atanPartial_valid r hr (2 * k),
    atanPartial_valid r hr (2 * k + 1)⟩

private theorem addEnds (a b : I)
    (ha : qValid a.lo = true ∧ qValid a.hi = true)
    (hb : qValid b.lo = true ∧ qValid b.hi = true) :
    (add a b).toBounds = RationalBounds.add a.toBounds b.toBounds := by
  exact congrArg₂ RationalBounds.mk
    (toRat_qAdd a.lo b.lo ha.1 hb.1)
    (toRat_qAdd a.hi b.hi ha.2 hb.2)

theorem halfAtanBounds_toBounds (r : QPair) (hr : qValid r = true) (k : ℕ) :
    (halfAtanBounds r k).toBounds =
      RationalBounds.add (smallArctanBounds (1 / 2) k)
        (smallArctanBounds r.toRat k) := by
  change (add (smallAtanBounds qHalf k) (smallAtanBounds r k)).toBounds = _
  rw [addEnds _ _ (atanEnds qHalf (by decide) k) (atanEnds r hr k),
    smallAtanBounds_toBounds qHalf (by decide) k,
    smallAtanBounds_toBounds r hr k, qHalf_toRat]

theorem halfAtan_ratio_sound {q r : QPair}
    (hq : qValid q = true) (hr : qValid r = true)
    (_hr0 : qLE qZero r = true) (hr1 : qLE r qHalf = true)
    (heq : qEq q
      (qDiv (qAdd qHalf r) (qSub qOne (qMul qHalf r))) = true) :
    q.toRat = ((1 / 2 : ℚ) + r.toRat) /
      (1 - (1 / 2 : ℚ) * r.toRat) := by
  let d := qSub qOne (qMul qHalf r)
  have hdval : qValid d = true :=
    qValid_qSub qValid_qOne (qValid_qMul (by decide) hr)
  have hden : d.toRat = 1 - (1 / 2 : ℚ) * r.toRat := by
    rw [toRat_qSub _ _ qValid_qOne (qValid_qMul (by decide) hr),
      toRat_qMul, qOne_toRat, qHalf_toRat]
  have hrle : r.toRat ≤ 1 / 2 := by
    simpa [qHalf_toRat] using! qLE_sound hr (by decide) hr1
  have hdpos : qLT qZero d = true := by
    apply qLT_complete qValid_qZero hdval
    rw [qZero_toRat, hden]
    linarith
  have hnumval : qValid (qAdd qHalf r) = true :=
    qValid_qAdd (by decide) hr
  have hdivval : qValid (qDiv (qAdd qHalf r) d) = true :=
    qValid_qDiv_pos hnumval hdpos
  have h := qEq_sound hq hdivval heq
  rw [toRat_qDiv_pos _ _ hdpos,
    toRat_qAdd _ _ (by decide : qValid qHalf = true) hr,
    qHalf_toRat, hden] at h
  exact h

theorem contains_atanHalf {q r : QPair} {k : ℕ}
    (hq : qValid q = true) (hr : qValid r = true)
    (hr0 : qLE qZero r = true) (hr1 : qLE r qHalf = true)
    (heq : qEq q
      (qDiv (qAdd qHalf r) (qSub qOne (qMul qHalf r))) = true) :
    (halfAtanBounds r k).toBounds.Contains (Real.arctan (q.toRat : ℝ)) := by
  rw [halfAtanBounds_toBounds r hr k]
  have h0 : 0 ≤ r.toRat := by
    simpa [qZero_toRat] using! qLE_sound qValid_qZero hr hr0
  have h1 : r.toRat ≤ 1 / 2 := by
    simpa [qHalf_toRat] using! qLE_sound hr (by decide) hr1
  exact contains_arctan_half_add q.toRat r.toRat k h0 h1
    (halfAtan_ratio_sound hq hr hr0 hr1 heq)

theorem inverseAtanBounds_toBounds (a : I) (ha : validI a = true) :
    (inverseAtanBounds a).toBounds =
      RationalBounds.add
        (RationalBounds.mul (RationalBounds.point (1 / 2))
          ParameterFamily.piBounds)
        (RationalBounds.neg a.toBounds) := by
  have hp : validI (mul (point qHalf) piBounds) = true := by decide
  have hpoint : validI (point qHalf) = true := by decide
  have hpi : validI piBounds = true := by decide
  obtain ⟨halo, hahi, _⟩ := validI_parts ha
  rw [show inverseAtanBounds a = add (mul (point qHalf) piBounds) (neg a) from rfl]
  rw [addEnds _ _ ⟨(validI_parts hp).1, (validI_parts hp).2.1⟩
    ⟨qValid_qNeg hahi, qValid_qNeg halo⟩]
  rw [toBounds_mul _ _ hpoint hpi, toBounds_neg, piBounds_toBounds]
  have hhalf : (point qHalf).toBounds = RationalBounds.point (1 / 2) := by
    simp [point, I.toBounds, RationalBounds.point, qHalf_toRat]
  rw [hhalf]

theorem contains_atanInverse {q r : QPair} {a : I}
    (hq : qValid q = true) (hr : qValid r = true)
    (hq0 : qLT qZero q = true) (heq : qEq r (qInv q) = true)
    (ha : validI a = true)
    (har : a.toBounds.Contains (Real.arctan (r.toRat : ℝ))) :
    (inverseAtanBounds a).toBounds.Contains (Real.arctan (q.toRat : ℝ)) := by
  rw [inverseAtanBounds_toBounds a ha]
  have hq0' : 0 < q.toRat := by
    simpa [qZero_toRat] using! qLT_sound qValid_qZero hq hq0
  have hr' : r.toRat = q.toRat⁻¹ := by
    have h := qEq_sound hr (qValid_qInv_pos q hq0) heq
    rwa [toRat_qInv_pos q hq0] at h
  exact contains_arctan_inverse q.toRat r.toRat hq0' hr' a.toBounds har

#print axioms contains_atanSmall
#print axioms contains_atanHalf
#print axioms contains_atanInverse

end Li2Unified.Proofs.Potential.KernelReflectionSelf

end


end
