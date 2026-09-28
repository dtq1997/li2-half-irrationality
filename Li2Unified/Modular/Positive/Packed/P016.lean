module
public import Li2Unified.Modular.Base.RestrictedSeriesCompat
public import Li2Unified.Modular.Positive.Packed.P015
public import Li2Unified.Modular.Base.OriginalFunctionalAssembly
public import Li2Unified.Modular.Base.FieldPoleSums
public import Li2Unified.Modular.Base.ReciprocalFunctional
public import Li2Unified.Modular.Base.DissectedSquareRecurrence
public import Li2Unified.Modular.Base.PulledPoleValues
public import Li2Unified.Modular.Positive.Packed.P001

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem generalOriginal_fieldPoleFunctional (μ : ℕ → ℤ_[p])
    (w : Fin p → (ℚ_[p])[X]) (m : ℕ) (hm : m < p * p)
    (F : ℚ[X]) (a : Fin p) :
    fieldPoleFunctional μ w (originalPulledRegular m F a)
      (generalOriginalPulledResidue m hm F a) =
    fieldPoleFunctional μ w
      (rationalPolynomialSeries ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ)))) 0 +
    ∑ j : ↥(Finset.Icc 1 m), C (originalResidue m F j.val : ℚ_[p]) *
      fieldPoleFunctional μ w (pulledPoleRegular j.val a.val)
        (generalPulledPoleResidue m j.val hm (Finset.mem_Icc.mp j.property).2 a) := by
  classical
  rw [originalPulledRegular_subtype]
  let f : ↥(Finset.Icc 1 m) → PowerSeries ℚ_[p] := fun j =>
    (originalResidue m F j.val : ℚ_[p]) • pulledPoleRegular j.val a.val
  have hf : ∀ j, PowerSeries.IsRestricted 1 (f j) := by
    intro j
    exact Li2.restrictedSeries_smul 1
      (pulledPoleRegular_isRestricted (p := p) j.val a.val)
      (originalResidue m F j.val : ℚ_[p])
  have hq : PowerSeries.IsRestricted 1
      (rationalPolynomialSeries (p := p)
        ((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ)))) :=
    field_polynomial_isRestricted
      (((F /ₘ D m).comp (C (p : ℚ) * X - C (a.val : ℚ))).map
        (Rat.castHom ℚ_[p]))
  have hr : generalOriginalPulledResidue m hm F a =
      0 + generalOriginalPulledResidue m hm F a := by simp
  rw [hr, fieldPoleFunctional_add μ w _ _ hq
    (field_sum_isRestricted Finset.univ f (fun j _ => hf j))]
  congr 1
  unfold generalOriginalPulledResidue
  rw [fieldPoleFunctional_sum μ w Finset.univ f (fun j _ => hf j)]
  apply Finset.sum_congr rfl
  intro j _
  exact fieldPoleFunctional_smul μ w _
    (pulledPoleRegular_isRestricted _ _) _ _

#print axioms generalOriginal_fieldPoleFunctional

end
end Li2Unified.Proofs.Hermite

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterReciprocalG_shift (z : ℚ)
    (hz0 : Li2.VG p z 0) (hz : Li2.VG p (z / (1 - z)) 0)
    (hz1 : z ≠ 1) (hzne : z ≠ 0)
    (d : ℚ) (hd : d ≠ 0) (hv : padicValRat p d = 0) (e k : ℕ) :
    (Li2.padicParameterG z hz
      (Li2.padicReciprocalSeries (d + (p : ℚ) * (k : ℚ))
        (Li2.rational_unit_add_prime_mul d hd hv k).1
        (Li2.rational_unit_add_prime_mul d hd hv k).2 e) : ℚ_[p]) =
      ((Li2.padicParameterG z hz (Li2.padicReciprocalSeries d hd hv e) : ℚ_[p]) -
        ∑ j ∈ Finset.range k, (z : ℚ_[p]) ^ (j + 1) *
          (((d : ℚ_[p]) + (p : ℚ_[p]) * ((j : ℚ_[p]) + 1)) ^ e)⁻¹) /
        (z : ℚ_[p]) ^ k := by
  rw [← Li2.padicReciprocalSeries_shift d hd hv e k,
    Li2.padicParameterG_shift z hz0 hz hz1 hzne _
      (Li2.padicReciprocalSeries_isRestricted d hd hv e) k]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [Li2.padicReciprocalSeries_eval_inv]
  simp only [PadicInt.coe_add, PadicInt.coe_natCast, PadicInt.coe_one]

#print axioms parameterReciprocalG_shift

end
end Li2Unified.Proofs.Hermite

end

section
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def parameterDissectedSquare (z : ℚ)
    (hz : Li2.VG p (z / (1 - z)) 0) (Y : ℚ_[p]) (m : ℕ) : ℚ_[p] :=
  if hm : p ∣ m + 1 then
    (p : ℚ_[p])⁻¹ ^ 2 * (z : ℚ_[p])⁻¹ ^ ((m + 1) / p - 1) *
      (Y - (Li2.parameterTau z ((m + 1) / p - 1) : ℚ_[p]))
  else
    (Li2.padicParameterG z hz
      (Li2.padicReciprocalSeries (((m + 1 : ℕ) : ℚ) - (p : ℚ))
        (Li2.rational_nonmultiple_sub_prime (m + 1) hm).1
        (Li2.rational_nonmultiple_sub_prime (m + 1) hm).2 2) : ℚ_[p])

theorem parameterDissectedSquare_matching (z : ℚ)
    (hz : Li2.VG p (z / (1 - z)) 0) (Y : ℚ_[p])
    (m : ℕ) (hm : p ∣ m + 1) :
    parameterDissectedSquare z hz Y m =
      (p : ℚ_[p])⁻¹ ^ 2 * (z : ℚ_[p])⁻¹ ^ ((m + 1) / p - 1) *
        (Y - (Li2.parameterTau z ((m + 1) / p - 1) : ℚ_[p])) := by
  simp only [parameterDissectedSquare, dif_pos hm]

theorem parameterDissectedSquare_nonmatching (z : ℚ)
    (hz : Li2.VG p (z / (1 - z)) 0) (Y : ℚ_[p])
    (m : ℕ) (hm : ¬p ∣ m + 1) :
    parameterDissectedSquare z hz Y m =
      (Li2.padicParameterG z hz
        (Li2.padicReciprocalSeries (((m + 1 : ℕ) : ℚ) - (p : ℚ))
          (Li2.rational_nonmultiple_sub_prime (m + 1) hm).1
          (Li2.rational_nonmultiple_sub_prime (m + 1) hm).2 2) : ℚ_[p]) := by
  simp only [parameterDissectedSquare, dif_neg hm]

theorem parameterDissectedSquare_step (z : ℚ)
    (hz0 : Li2.VG p z 0) (hz : Li2.VG p (z / (1 - z)) 0)
    (hz1 : z ≠ 1) (hzne : z ≠ 0) (Y : ℚ_[p]) (m : ℕ) :
    (z : ℚ_[p]) * parameterDissectedSquare z hz Y (m + p) =
      parameterDissectedSquare z hz Y m -
        (z : ℚ_[p]) / ((m : ℚ_[p]) + 1) ^ 2 := by
  by_cases hm : p ∣ m + 1
  · have hm' : p ∣ m + p + 1 := (Li2.prime_dvd_step_iff m).mpr hm
    rw [parameterDissectedSquare_matching z hz Y m hm,
      parameterDissectedSquare_matching z hz Y (m + p) hm']
    have hq : 0 < (m + 1) / p :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hm) (Fact.out : p.Prime).pos
    have hdiv : (m + p + 1) / p - 1 = ((m + 1) / p - 1) + 1 := by
      rw [show m + p + 1 = (m + 1) + p by omega,
        Nat.add_div_right _ (Fact.out : p.Prime).pos]
      omega
    have he : (m : ℚ_[p]) + 1 =
        (p : ℚ_[p]) * ((((m + 1) / p - 1 : ℕ) : ℚ_[p])) + (p : ℚ_[p]) := by
      have hh : m + 1 = p * ((m + 1) / p - 1) + p := by
        have ht := Nat.mul_div_cancel' hm
        rw [show (m + 1) / p = ((m + 1) / p - 1) + 1 by omega,
          Nat.mul_add, Nat.mul_one] at ht
        omega
      exact_mod_cast hh
    rw [hdiv, he]
    convert Li2.matching_square_step z hzne Y ((m + 1) / p - 1) using 1; ring
  · have hm' : ¬p ∣ m + p + 1 :=
      fun h => hm ((Li2.prime_dvd_step_iff m).mp h)
    rw [parameterDissectedSquare_nonmatching z hz Y m hm,
      parameterDissectedSquare_nonmatching z hz Y (m + p) hm']
    let d : ℚ := (((m + 1 : ℕ) : ℚ) - (p : ℚ))
    have hd := Li2.rational_nonmultiple_sub_prime (m + 1) hm
    have h := parameterReciprocalG_shift z hz0 hz hz1 hzne d hd.1 hd.2 2 1
    have hshift : d + (p : ℚ) * ((1 : ℕ) : ℚ) =
        (((m + p + 1 : ℕ) : ℚ) - (p : ℚ)) := by
      dsimp [d]
      push_cast
      ring
    simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add] at h
    have he : (d : ℚ_[p]) + (p : ℚ_[p]) = (m : ℚ_[p]) + 1 := by
      dsimp [d]
      push_cast
      ring
    rw [mul_one, he] at h
    have hzn : (z : ℚ_[p]) ≠ 0 := by exact_mod_cast hzne
    have hh := (eq_div_iff hzn).mp h
    have hs := Li2.padicReciprocalSeries_congr _ _ hshift
      (Li2.rational_unit_add_prime_mul d hd.1 hd.2 1).1
      (Li2.rational_unit_add_prime_mul d hd.1 hd.2 1).2
      (Li2.rational_nonmultiple_sub_prime (m + p + 1) hm').1
      (Li2.rational_nonmultiple_sub_prime (m + p + 1) hm').2 2
    rw [hs] at hh
    simpa only [d, div_eq_mul_inv, mul_comm] using hh

#print axioms parameterDissectedSquare_step

end
end Li2Unified.Proofs.Hermite

end

section
open Li2 Li2Unified.Proofs.Hermite
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem parameter_nonmatching_pole_contribution (z : ℚ) (hreg : VG p (z/(1-z)) 0)
    (Y : ℚ_[p]) (j a : ℕ) (ha : a < p) (hm : ¬p ∣ j+(p-1-a)+1) :
    (restrictedU (integralParameterMoment z hreg)
      (padicReciprocalSeries (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))
        (rational_nonmultiple_sub_prime _ hm).1 (rational_nonmultiple_sub_prime _ hm).2 1) : ℚ_[p])-
    (a:ℚ_[p])/(p:ℚ_[p])*(restrictedV (integralParameterMoment z hreg)
      (padicReciprocalSeries (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))
        (rational_nonmultiple_sub_prime _ hm).1 (rational_nonmultiple_sub_prime _ hm).2 1) : ℚ_[p]) =
    (j:ℚ_[p])*parameterDissectedSquare z hreg Y (j+(p-1-a)) := by
  rw [reciprocal_differential_correction,
    parameterDissectedSquare_nonmatching z hreg Y _ hm]
  have he : ((((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ)):ℚ_[p])+(a:ℚ_[p]) = (j:ℚ_[p]) := by
    exact_mod_cast polePullback_denominator (p := p) j a ha
  simp only [Rat.cast_sub] at *
  rw [he]
  rfl

theorem parameter_matching_pole_contribution (z : ℚ) (hreg : VG p (z/(1-z)) 0)
    (Y : ℚ_[p]) (j a : ℕ) (ha : a < p) (hm : p ∣ j+(p-1-a)+1) :
    let k := (j+(p-1-a)+1)/p-1
    (p:ℚ_[p])⁻¹*((k:ℚ_[p])*(z:ℚ_[p])⁻¹^k*
      (Y-(parameterTau z k:ℚ_[p]))-
      (a:ℚ_[p])/(p:ℚ_[p])*(-(z:ℚ_[p])⁻¹^k*
        (Y-(parameterTau z k:ℚ_[p])))) =
    (j:ℚ_[p])*parameterDissectedSquare z hreg Y (j+(p-1-a)) := by
  dsimp only
  rw [parameterDissectedSquare_matching z hreg Y _ hm]
  have hq : 0 < (j+(p-1-a)+1)/p :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hm) hp.out.pos
  have he : j = p*((j+(p-1-a)+1)/p-1)+a := by
    have ht := Nat.mul_div_cancel' hm
    rw [show (j+(p-1-a)+1)/p = ((j+(p-1-a)+1)/p-1)+1 by omega,
      Nat.mul_add, Nat.mul_one] at ht
    have hi := polePullback_index j a ha
    omega
  have hj : (j:ℚ_[p]) = (p:ℚ_[p])*(((j+(p-1-a)+1)/p-1:ℕ):ℚ_[p])+(a:ℚ_[p]) := by
    exact_mod_cast he
  rw [hj]
  have hpne : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  field_simp
  <;> ring

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameter_nonmatching_pole_contribution
#print axioms Li2Unified.Proofs.PrimeEdge.parameter_matching_pole_contribution

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def parameterPoleWindow (lam : ℚ)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (Y : ℚ_[p]) (j : ℕ) : ℚ_[p] :=
  Li2.poleDissectionWindow (lam : ℚ_[p]) p
    (parameterDissectedSquare (lam ^ p) hz Y) j

theorem parameterPoleWindow_telescope (lam : ℚ)
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (Y : ℚ_[p]) (j : ℕ) :
    (lam : ℚ_[p]) ^ j * parameterPoleWindow lam hz Y j =
      parameterPoleWindow lam hz Y 0 - (Li2.parameterTau lam j : ℚ_[p]) := by
  let F : ℕ → ℚ_[p] := parameterDissectedSquare (lam ^ p) hz Y
  let B : ℕ → ℚ_[p] := fun k => (((k : ℚ_[p]) + 1) ^ 2)⁻¹
  have hF : ∀ k, (lam : ℚ_[p]) ^ p * F (k + p) =
      F k - (lam : ℚ_[p]) ^ p * B k := by
    intro k
    simpa [F, B, div_eq_mul_inv] using
      parameterDissectedSquare_step (lam ^ p) hz0 hz hz1
        (pow_ne_zero p hzne) Y k
  have ht := Li2.poleDissectionWindow_telescope (lam : ℚ_[p])
    (by exact_mod_cast hzne) p (Fact.out : p.Prime).pos F B hF j
  have htau : (∑ b ∈ Finset.range j, (lam : ℚ_[p]) ^ (b + 1) * B b) =
      (Li2.parameterTau lam j : ℚ_[p]) := by
    rw [Li2.parameterTau_eq_range]
    push_cast
    apply Finset.sum_congr rfl
    intro b _
    simp [B, div_eq_mul_inv]
  simpa only [parameterPoleWindow, F, htau] using ht

def parameterPoleEta (lam : ℚ)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0) : ℚ_[p] :=
  (lam : ℚ_[p])⁻¹ ^ (p - 1) *
    ∑ b ∈ Finset.range (p - 1), (lam : ℚ_[p]) ^ b *
      parameterDissectedSquare (lam ^ p) hz 0 b

theorem parameterPoleWindow_origin (lam : ℚ) (hzne : lam ≠ 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0) (Y : ℚ_[p]) :
    parameterPoleWindow lam hz Y 0 =
      parameterPoleEta lam hz + (p : ℚ_[p])⁻¹ ^ 2 * Y := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have htopIndex : p - 1 + 1 = p := by omega
  have htop : parameterDissectedSquare (lam ^ p) hz Y (p - 1) =
      (p : ℚ_[p])⁻¹ ^ 2 * Y := by
    rw [parameterDissectedSquare_matching (lam ^ p) hz Y (p - 1)
      (by rw [htopIndex])]
    rw [htopIndex, Nat.div_self hp]
    simp [Li2.parameterTau]
  have hlow : (∑ b ∈ Finset.range (p - 1), (lam : ℚ_[p]) ^ b *
        parameterDissectedSquare (lam ^ p) hz Y b) =
      ∑ b ∈ Finset.range (p - 1), (lam : ℚ_[p]) ^ b *
        parameterDissectedSquare (lam ^ p) hz 0 b := by
    apply Finset.sum_congr rfl
    intro b hb
    have hb0 : 0 < b + 1 := by omega
    have hbp : b + 1 < p := by have := Finset.mem_range.mp hb; omega
    have hnot : ¬p ∣ b + 1 := Nat.not_dvd_of_pos_of_lt hb0 hbp
    rw [parameterDissectedSquare_nonmatching (lam ^ p) hz Y b hnot,
      parameterDissectedSquare_nonmatching (lam ^ p) hz 0 b hnot]
  have hcancel : (lam : ℚ_[p])⁻¹ ^ (p - 1) * (lam : ℚ_[p]) ^ (p - 1) = 1 := by
    have hl : (lam : ℚ_[p]) ≠ 0 := by exact_mod_cast hzne
    rw [inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero _ hl)
  have hr : Finset.range p = Finset.range ((p - 1) + 1) :=
    congrArg Finset.range htopIndex.symm
  unfold parameterPoleWindow parameterPoleEta Li2.poleDissectionWindow
  simp only [zero_add]
  rw [hr, Finset.sum_range_succ, hlow, htop]
  rw [mul_add]
  calc
    _ = (lam : ℚ_[p])⁻¹ ^ (p - 1) *
          (∑ b ∈ Finset.range (p - 1), (lam : ℚ_[p]) ^ b *
            parameterDissectedSquare (lam ^ p) hz 0 b) +
          (p : ℚ_[p])⁻¹ ^ 2 * Y := by rw [← mul_assoc, hcancel, one_mul]
    _ = _ := rfl

theorem parameterPoleWindow_affine (lam : ℚ)
    (hzne : lam ≠ 0) (hz0 : Li2.VG p (lam ^ p) 0)
    (hz : Li2.VG p (lam ^ p / (1 - lam ^ p)) 0)
    (hz1 : lam ^ p ≠ 1) (Y : ℚ_[p]) (j : ℕ) :
    parameterPoleWindow lam hz Y j =
      (lam : ℚ_[p])⁻¹ ^ j *
        (parameterPoleEta lam hz + (p : ℚ_[p])⁻¹ ^ 2 * Y -
          (Li2.parameterTau lam j : ℚ_[p])) := by
  have hl : (lam : ℚ_[p]) ≠ 0 := by exact_mod_cast hzne
  have h := parameterPoleWindow_telescope lam hzne hz0 hz hz1 Y j
  rw [parameterPoleWindow_origin lam hzne hz Y] at h
  calc
    parameterPoleWindow lam hz Y j =
        ((lam : ℚ_[p]) ^ j)⁻¹ *
          ((lam : ℚ_[p]) ^ j * parameterPoleWindow lam hz Y j) := by
      field_simp [pow_ne_zero j hl]
    _ = ((lam : ℚ_[p]) ^ j)⁻¹ *
          (parameterPoleEta lam hz + (p : ℚ_[p])⁻¹ ^ 2 * Y -
            (Li2.parameterTau lam j : ℚ_[p])) := by rw [h]
    _ = _ := by rw [← inv_pow]

end
end Li2Unified.Proofs.Hermite

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Proofs.Hermite
noncomputable section

end
end Li2Unified.Proofs.Hermite

end

end
