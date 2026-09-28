module
public import Li2Unified.Modular.Positive.Packed.P107
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic
public import Li2Unified.Modular.Positive.Packed.P106
public import Mathlib.Analysis.Real.Pi.Bounds
public import Li2Unified.Modular.Positive.Packed.P164

set_option backward.privateInPublic true

@[expose] public section

section
/-! A sound two-term correction from a reusable dyadic log anchor. -/
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily

def anchoredLogBounds (k : ℤ) (u rho : ℚ) : RationalBounds :=
  RationalBounds.add (scaledLogBounds k u 24)
    (RationalBounds.neg (reducedLogBounds rho 2))

theorem contains_anchored_log (q u rho : ℚ) (k : ℤ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hq : q = (2:ℚ)^k*u/rho) :
    (anchoredLogBounds k u rho).Contains (Real.log (q:ℝ)) := by
  have hscaled : (scaledLogBounds k u 24).Contains
      (Real.log (((2:ℚ)^k*u:ℚ):ℝ)) :=
    contains_scaled_log ((2:ℚ)^k*u) u k 24 hu hu1 rfl
  have hratio := contains_reduced_log rho hrho hrho1 2
  have h := RationalBounds.contains_add hscaled
    (RationalBounds.contains_neg hratio)
  have hreal : Real.log (q:ℝ) =
      Real.log (((2:ℚ)^k*u:ℚ):ℝ)-Real.log (rho:ℝ) := by
    rw [hq, Rat.cast_div]
    exact Real.log_div
      (by positivity : (((2:ℚ)^k*u:ℚ):ℝ) ≠ 0)
      (by exact_mod_cast hrho.ne')
  rw [hreal]
  exact h

end
end Li2Unified.Proofs.Potential

end

section
/-! Finite rational bounds from the actual arctangent series.
These are reusable inequalities, not a certificate checker or energy theorem. -/
open Filter Finset
open scoped Topology
namespace Li2Unified.ParameterFamily
noncomputable section

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "ElementaryBounds: imports loaded"
  out.flush

lemma arctan_term_antitone (x : ℝ) (hx : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun n : ℕ => x^(2*n+1) / ((2*n+1:ℕ):ℝ)) := by
  intro m n hmn
  apply div_le_div₀ (pow_nonneg hx _)
  · exact pow_le_pow_of_le_one hx h1 (by omega)
  · positivity
  · exact_mod_cast (show 2*m+1 ≤ 2*n+1 by omega)

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "ElementaryBounds: antitone complete"
  out.flush

theorem arctan_series_bounds (x : ℝ) (hx : 0 ≤ x) (h1 : x < 1) (k : ℕ) :
    (∑ i ∈ range (2*k), (-1:ℝ)^i * (x^(2*i+1) / ((2*i+1:ℕ):ℝ))) ≤ Real.arctan x ∧
    Real.arctan x ≤ ∑ i ∈ range (2*k+1),
      (-1:ℝ)^i * (x^(2*i+1) / ((2*i+1:ℕ):ℝ)) := by
  have hs := Real.hasSum_arctan (x := x) (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using! h1)
  have ht : Tendsto (fun n : ℕ => ∑ i ∈ range n,
      (-1:ℝ)^i * (x^(2*i+1) / ((2*i+1:ℕ):ℝ))) atTop (𝓝 (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc] using! hs.tendsto_sum_nat
  exact ⟨Antitone.alternating_series_le_tendsto ht (arctan_term_antitone x hx h1.le) k,
    Antitone.tendsto_le_alternating_series ht (arctan_term_antitone x hx h1.le) k⟩

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "ElementaryBounds: series bounds complete"
  out.flush

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "ElementaryBounds: final bound complete"
  out.flush

end
end Li2Unified.ParameterFamily

end

section
/-! Exact rational arctangent endpoint enclosures. The addition and
reciprocal reductions carry explicit equalities and branch hypotheses. -/
open Finset
namespace Li2Unified.ParameterFamily
noncomputable section

def arctanPartial (r : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (-1:ℚ)^i * (r^(2*i+1) / ((2*i+1:ℕ):ℚ))

def smallArctanBounds (r : ℚ) (k : ℕ) : RationalBounds :=
  ⟨arctanPartial r (2*k), arctanPartial r (2*k+1)⟩

theorem contains_small_arctan (r : ℚ) (hr : 0 ≤ r) (h1 : r < 1) (k : ℕ) :
    (smallArctanBounds r k).Contains (Real.arctan (r:ℝ)) := by
  have h := arctan_series_bounds (r:ℝ) (by exact_mod_cast hr) (by exact_mod_cast h1) k
  simpa only [RationalBounds.Contains, smallArctanBounds, arctanPartial,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, Rat.cast_natCast, Rat.cast_add, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using! h

def piBounds : RationalBounds := ⟨3141592/10^6,3141593/10^6⟩

theorem contains_pi : piBounds.Contains Real.pi := by
  convert And.intro Real.pi_gt_d6.le Real.pi_lt_d6.le using 1 <;>
    norm_num [RationalBounds.Contains, piBounds]

theorem contains_arctan_half_add (q r : ℚ) (k : ℕ)
    (hr : 0 ≤ r) (h1 : r ≤ 1/2)
    (hq : q = ((1/2:ℚ)+r)/(1-(1/2)*r)) :
    (RationalBounds.add (smallArctanBounds (1/2) k) (smallArctanBounds r k)).Contains
      (Real.arctan (q:ℝ)) := by
  have hr' : (r:ℝ) ≤ 1/2 := by
    have h : (r:ℝ) ≤ ((1/2:ℚ):ℝ) := by exact_mod_cast h1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using! h
  have hq' : (q:ℝ) = ((1/2:ℝ)+r)/(1-(1/2)*r) := by
    simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_one, Rat.cast_ofNat] using! congrArg (fun z : ℚ => (z : ℝ)) hq
  have hsum := RationalBounds.contains_add
    (contains_small_arctan (1/2) (by norm_num) (by norm_num) k)
    (contains_small_arctan r hr (by linarith) k)
  have ha := Real.arctan_add (x := (1/2:ℝ)) (y := (r:ℝ)) (by linarith)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hsum
  rw [ha, ← hq'] at hsum
  exact hsum

theorem contains_arctan_inverse (q r : ℚ) (hq : 0 < q) (hr : r = q⁻¹)
    (a : RationalBounds) (ha : a.Contains (Real.arctan (r:ℝ))) :
    (RationalBounds.add
      (RationalBounds.mul (RationalBounds.point (1/2)) piBounds)
      (RationalBounds.neg a)).Contains (Real.arctan (q:ℝ)) := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have he : (1/2:ℝ)*Real.pi + -Real.arctan (r:ℝ) = Real.arctan (q:ℝ) := by
    rw [hr, Rat.cast_inv, Real.arctan_inv_of_pos hq']
    ring
  have h := RationalBounds.contains_add
    (RationalBounds.contains_mul (RationalBounds.contains_point (1/2)) contains_pi)
    (RationalBounds.contains_neg ha)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  rwa [he] at h

end
end Li2Unified.ParameterFamily

end

section
/-! Sound semantic steps for the potential certificate's nonlinear nodes. -/
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily

theorem contains_mulLogAbs_quarter {a logLo logHi : RationalBounds} {x : ℝ}
    (hx : a.Contains x) (ha : 0 ≤ a.lower) (hquarter : a.upper ≤ 1/4)
    (hlo : logLo.Contains (Real.log (a.lower:ℝ)))
    (hhi : logHi.Contains (Real.log (a.upper:ℝ))) :
    (RationalBounds.mk (a.upper*logHi.lower) (a.lower*logLo.upper)).Contains
      (mulLogAbs x) := by
  have ha' : (0:ℝ) ≤ a.lower := by exact_mod_cast ha
  have hb' : (a.upper:ℝ) ≤ 1/4 := by
    simpa using! (Rat.cast_le.mpr hquarter : (a.upper:ℝ) ≤ ((1/4:ℚ):ℝ))
  have h := mulLogAbs_antitone_quarter ha' hx.1 hx.2 hb'
  constructor
  · change ((a.upper*logHi.lower:ℚ):ℝ) ≤ mulLogAbs x
    rw [Rat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hhi.1 ((ha'.trans hx.1).trans hx.2)).trans h.1
  · change mulLogAbs x ≤ ((a.lower*logLo.upper:ℚ):ℝ)
    rw [Rat.cast_mul]
    exact h.2.trans (mul_le_mul_of_nonneg_left hlo.2 ha')

theorem contains_mulLogAbs_cross {x : ℝ} {r logLower : ℚ}
    (hr : 0 ≤ r) (hrQuarter : r ≤ 1/4)
    (hx : |x| ≤ (r:ℝ))
    (hlog : (logLower:ℝ) ≤ Real.log (r:ℝ)) :
    (RationalBounds.mk (r*logLower) (-r*logLower)).Contains (mulLogAbs x) := by
  have hr' : ((r:ℝ) ≤ 1/4) := by
    simpa using! (Rat.cast_le.mpr hrQuarter : (r:ℝ) ≤ ((1/4:ℚ):ℝ))
  have hr0 : (0:ℝ) ≤ r := by exact_mod_cast hr
  have h := mulLogAbs_cross_zero hx hr'
  have hb : -(r:ℝ)*Real.log (r:ℝ) ≤ -(r:ℝ)*(logLower:ℝ) := by
    exact mul_le_mul_of_nonpos_left hlog (by linarith)
  have habs := abs_le.mp (h.trans hb)
  constructor
  · change ((r*logLower:ℚ):ℝ) ≤ mulLogAbs x
    push_cast
    linarith [habs.1]
  · change mulLogAbs x ≤ ((-r*logLower:ℚ):ℝ)
    push_cast
    linarith [habs.2]

end
end Li2Unified.Proofs.Potential

end

section
/-! Real soundness of the reflection checker's algebraic and endpoint steps.
The checker supplies the Boolean enclosures; predecessor values and analytic
endpoint bounds are explicit hypotheses. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section
open Li2Unified.ParameterFamily

theorem contains_of_encloses {out candidate : I} {x : ℝ}
    (hx : candidate.toBounds.Contains x)
    (hc : encloses out candidate = true) : out.toBounds.Contains x := by
  exact RationalBounds.contains_widen hx (encloses_sound hc).1 (encloses_sound hc).2

theorem add_sound {out a b : I} {x y : ℝ}
    (ha : validI a = true) (hb : validI b = true)
    (hx : a.toBounds.Contains x) (hy : b.toBounds.Contains y)
    (hc : encloses out (add a b) = true) :
    out.toBounds.Contains (x + y) := by
  apply contains_of_encloses ?_ hc
  rw [toBounds_add a b ha hb]
  exact RationalBounds.contains_add hx hy

theorem neg_sound {out a : I} {x : ℝ}
    (hx : a.toBounds.Contains x)
    (hc : encloses out (neg a) = true) :
    out.toBounds.Contains (-x) := by
  apply contains_of_encloses ?_ hc
  rw [toBounds_neg a]
  exact RationalBounds.contains_neg hx

theorem mul_sound {out a b : I} {x y : ℝ}
    (ha : validI a = true) (hb : validI b = true)
    (hx : a.toBounds.Contains x) (hy : b.toBounds.Contains y)
    (hc : encloses out (mul a b) = true) :
    out.toBounds.Contains (x * y) := by
  apply contains_of_encloses ?_ hc
  rw [toBounds_mul a b ha hb]
  exact RationalBounds.contains_mul hx hy

theorem log_sound {out a lo hi : I} {x : ℝ}
    (ha : validI a = true) (hp : qLT qZero a.lo = true)
    (hx : a.toBounds.Contains x)
    (hlo : lo.toBounds.Contains (Real.log (a.lo.toRat : ℝ)))
    (hhi : hi.toBounds.Contains (Real.log (a.hi.toRat : ℝ)))
    (hc : encloses out ⟨lo.lo, hi.hi⟩ = true) :
    out.toBounds.Contains (Real.log x) := by
  have hpos : 0 < a.toBounds.lower := by
    have h := qLT_sound (by decide : qValid qZero = true) (validI_parts ha).1 hp
    simpa only [I.toBounds, qZero, QPair.toRat, Int.cast_zero, Nat.cast_one,
      zero_div] using! h
  apply contains_of_encloses ?_ hc
  exact RationalBounds.contains_log hx hpos hlo.1 hhi.2

theorem atan_sound {out a lo hi : I} {x : ℝ}
    (hx : a.toBounds.Contains x)
    (hlo : lo.toBounds.Contains (Real.arctan (a.lo.toRat : ℝ)))
    (hhi : hi.toBounds.Contains (Real.arctan (a.hi.toRat : ℝ)))
    (hc : encloses out ⟨lo.lo, hi.hi⟩ = true) :
    out.toBounds.Contains (Real.arctan x) := by
  apply contains_of_encloses ?_ hc
  exact RationalBounds.contains_arctan hx hlo.1 hhi.2

theorem h_positive_from_product_bound {out a witness : I} {x : ℝ}
    (ha : validI a = true) (hzero : qLE qZero a.lo = true)
    (hx : a.toBounds.Contains x)
    (hw : witness.toBounds.Contains (x * Real.log x))
    (hc : encloses out witness = true) :
    out.toBounds.Contains (mulLogAbs x) := by
  have ha0 : 0 ≤ a.toBounds.lower := by
    have h := qLE_sound (by decide : qValid qZero = true) (validI_parts ha).1 hzero
    simpa only [I.toBounds, qZero, QPair.toRat, Int.cast_zero, Nat.cast_one,
      zero_div] using! h
  have hx0 : 0 ≤ x := (by exact_mod_cast ha0 : (0 : ℝ) ≤ (a.toBounds.lower : ℝ)).trans hx.1
  apply contains_of_encloses ?_ hc
  rw [mulLogAbs_nonneg x hx0]
  exact hw

theorem h_quarter_sound {out a logLo logHi : I} {x : ℝ}
    (ha : validI a = true)
    (hzero : qLE qZero a.lo = true)
    (hquarter : qLE a.hi qQuarter = true)
    (hx : a.toBounds.Contains x)
    (hlo : logLo.toBounds.Contains (Real.log (a.lo.toRat : ℝ)))
    (hhi : logHi.toBounds.Contains (Real.log (a.hi.toRat : ℝ)))
    (hc : encloses out ⟨qMul a.hi logHi.lo, qMul a.lo logLo.hi⟩ = true) :
    out.toBounds.Contains (mulLogAbs x) := by
  obtain ⟨halo, hahi, _⟩ := validI_parts ha
  have ha0 : 0 ≤ a.toBounds.lower := by
    have h := qLE_sound (by decide : qValid qZero = true) halo hzero
    simpa only [I.toBounds, qZero, QPair.toRat, Int.cast_zero, Nat.cast_one,
      zero_div] using! h
  have haq : a.toBounds.upper ≤ 1 / 4 := by
    have h := qLE_sound hahi (by decide : qValid qQuarter = true) hquarter
    simpa [I.toBounds, qQuarter, QPair.toRat] using! h
  have hbase := contains_mulLogAbs_quarter hx ha0 haq hlo hhi
  apply contains_of_encloses ?_ hc
  simpa only [I.toBounds, toRat_qMul] using! hbase

theorem h_cross_sound {out a logRadius : I} {radius : QPair} {x : ℝ}
    (ha : validI a = true) (hr : qValid radius = true)
    (hzero : qLE qZero radius = true)
    (hquarter : qLE radius qQuarter = true)
    (hleft : qLE (qNeg radius) a.lo = true)
    (hright : qLE a.hi radius = true)
    (hx : a.toBounds.Contains x)
    (hlog : logRadius.toBounds.Contains (Real.log (radius.toRat : ℝ)))
    (hc : encloses out
      ⟨qMul radius logRadius.lo, qNeg (qMul radius logRadius.lo)⟩ = true) :
    out.toBounds.Contains (mulLogAbs x) := by
  obtain ⟨halo, hahi, _⟩ := validI_parts ha
  have hr0 : 0 ≤ radius.toRat := by
    have h := qLE_sound (by decide : qValid qZero = true) hr hzero
    simpa [qZero, QPair.toRat] using! h
  have hrq : radius.toRat ≤ 1 / 4 := by
    have h := qLE_sound hr (by decide : qValid qQuarter = true) hquarter
    simpa [qQuarter, QPair.toRat] using! h
  have hl : -(radius.toRat) ≤ a.toBounds.lower := by
    have h := qLE_sound (qValid_qNeg hr) halo hleft
    simpa only [I.toBounds, toRat_qNeg] using! h
  have hu : a.toBounds.upper ≤ radius.toRat := qLE_sound hahi hr hright
  have hxabs : |x| ≤ (radius.toRat : ℝ) := by
    apply abs_le.mpr
    constructor
    · have hlR : -(radius.toRat : ℝ) ≤ (a.toBounds.lower : ℝ) := by
        exact_mod_cast hl
      exact hlR.trans hx.1
    · have huR : (a.toBounds.upper : ℝ) ≤ (radius.toRat : ℝ) := by
        exact_mod_cast hu
      exact hx.2.trans huR
  have hbase := contains_mulLogAbs_cross hr0 hrq hxabs hlog.1
  apply contains_of_encloses ?_ hc
  simpa only [I.toBounds, toRat_qMul, toRat_qNeg, neg_mul] using! hbase

end
end Li2Unified.Proofs.Potential.KernelReflectionSelf

#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.contains_of_encloses
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.add_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.neg_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.mul_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.log_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.atan_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.h_positive_from_product_bound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.h_quarter_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.h_cross_sound

end

end
