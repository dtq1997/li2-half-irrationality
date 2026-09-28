module
public import Li2Unified.Modular.Base.DissectedSquare

set_option backward.privateInPublic true

@[expose] public section

/-! Identify each independently constructed square term with the U/V
contribution of the pulled-back simple pole 1/(pu+j-a). Matching factors
are scaled simple poles; nonmatching factors are actual restricted inverses. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma polePullback_index (j a : ℕ) (ha : a < p) :
    j+(p-1-a)+1+a = j+p := by omega

lemma polePullback_denominator (j a : ℕ) (ha : a < p) :
    (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))+(a:ℚ) = (j:ℚ) := by
  have h := congrArg (fun n : ℕ => (n:ℚ)) (polePullback_index j a ha)
  push_cast at h ⊢
  linarith

theorem nonmatching_pole_contribution (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Y : ℚ_[p]) (j a : ℕ) (ha : a < p) (hm : ¬p ∣ j+(p-1-a)+1) :
    (restrictedU (integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral hp2 hp3))
      (padicReciprocalSeries (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))
        (rational_nonmultiple_sub_prime _ hm).1 (rational_nonmultiple_sub_prime _ hm).2 1) : ℚ_[p])-
    (a:ℚ_[p])/(p:ℚ_[p])*(restrictedV (integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral hp2 hp3))
      (padicReciprocalSeries (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))
        (rational_nonmultiple_sub_prime _ hm).1 (rational_nonmultiple_sub_prime _ hm).2 1) : ℚ_[p]) =
    (j:ℚ_[p])*dissectedSquare hp2 hp3 Y (j+(p-1-a)) := by
  rw [reciprocal_differential_correction,
    dissectedSquare_nonmatching hp2 hp3 Y _ hm]
  have he : ((((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ)):ℚ_[p])+(a:ℚ_[p]) = (j:ℚ_[p]) := by
    exact_mod_cast polePullback_denominator (p := p) j a ha
  simp only [Rat.cast_sub] at *
  rw [he]
  rfl

theorem matching_pole_contribution (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Y : ℚ_[p]) (j a : ℕ) (ha : a < p) (hm : p ∣ j+(p-1-a)+1) :
    let k := (j+(p-1-a)+1)/p-1
    (p:ℚ_[p])⁻¹*((k:ℚ_[p])*(primeParameter p:ℚ_[p])⁻¹^k*
      (Y-(parameterTau (primeParameter p) k:ℚ_[p]))-
      (a:ℚ_[p])/(p:ℚ_[p])*(-(primeParameter p:ℚ_[p])⁻¹^k*
        (Y-(parameterTau (primeParameter p) k:ℚ_[p])))) =
    (j:ℚ_[p])*dissectedSquare hp2 hp3 Y (j+(p-1-a)) := by
  dsimp only
  rw [dissectedSquare_matching hp2 hp3 Y _ hm]
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


def pulledSimplePoleContribution (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Y : ℚ_[p]) (j a : ℕ) : ℚ_[p] :=
  let m := j+(p-1-a)
  if hm : p ∣ m+1 then
    let k := (m+1)/p-1
    (p:ℚ_[p])⁻¹*((k:ℚ_[p])*(primeParameter p:ℚ_[p])⁻¹^k*
      (Y-(parameterTau (primeParameter p) k:ℚ_[p]))-
      (a:ℚ_[p])/(p:ℚ_[p])*(-(primeParameter p:ℚ_[p])⁻¹^k*
        (Y-(parameterTau (primeParameter p) k:ℚ_[p]))))
  else
    let f := padicReciprocalSeries (((m+1:ℕ):ℚ)-(p:ℚ))
      (rational_nonmultiple_sub_prime _ hm).1 (rational_nonmultiple_sub_prime _ hm).2 1
    let μ := integralParameterMoment (primeParameter p) (primeParameter_moment_integral hp2 hp3)
    (restrictedU μ f:ℚ_[p])-(a:ℚ_[p])/(p:ℚ_[p])*(restrictedV μ f:ℚ_[p])

theorem pulledSimplePoleContribution_eq (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (Y : ℚ_[p]) (j a : ℕ) (ha : a < p) :
    pulledSimplePoleContribution hp2 hp3 Y j a =
      (j:ℚ_[p])*dissectedSquare hp2 hp3 Y (j+(p-1-a)) := by
  unfold pulledSimplePoleContribution
  dsimp only
  split_ifs with hm
  · exact matching_pole_contribution hp2 hp3 Y j a ha hm
  · exact nonmatching_pole_contribution hp2 hp3 Y j a ha hm

end
end Li2

end
