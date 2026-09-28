module
public import Li2Unified.Modular.Base.DissectedSquare

set_option backward.privateInPublic true

@[expose] public section

/-! The concrete p-step recurrence, derived separately in the matching and
nonmatching cases. It discharges the hypothesis of the finite-window lemma. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma matching_square_step (z : ℚ) (hz : z ≠ 0) (Y : ℚ_[p]) (k : ℕ) :
    (z:ℚ_[p])*((p:ℚ_[p])⁻¹^2*(z:ℚ_[p])⁻¹^(k+1)*
      (Y-(parameterTau z (k+1):ℚ_[p]))) =
    (p:ℚ_[p])⁻¹^2*(z:ℚ_[p])⁻¹^k*(Y-(parameterTau z k:ℚ_[p]))-
      (z:ℚ_[p])/((p:ℚ_[p])*((k:ℚ_[p])+1))^2 := by
  have hz' : (z:ℚ_[p]) ≠ 0 := by exact_mod_cast hz
  have hp' : (p:ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hk : (k:ℚ_[p])+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  rw [parameterTau_succ]
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_one, pow_succ, inv_pow]
  push_cast
  field_simp
  <;> ring

lemma prime_dvd_step_iff (m : ℕ) : p ∣ m+p+1 ↔ p ∣ m+1 := by
  rw [show m+p+1 = (m+1)+p by omega]
  exact (Nat.dvd_add_iff_left (dvd_refl p)).symm

theorem dissectedSquare_step (hp2 : p ≠ 2) (hp3 : p ≠ 3) (Y : ℚ_[p]) (m : ℕ) :
    (primeParameter p:ℚ_[p])*dissectedSquare hp2 hp3 Y (m+p) =
      dissectedSquare hp2 hp3 Y m-(primeParameter p:ℚ_[p])/((m:ℚ_[p])+1)^2 := by
  by_cases hm : p ∣ m+1
  · have hm' : p ∣ m+p+1 := (prime_dvd_step_iff m).mpr hm
    rw [dissectedSquare_matching hp2 hp3 Y m hm,
      dissectedSquare_matching hp2 hp3 Y (m+p) hm']
    have hq : 0 < (m+1)/p := Nat.div_pos (Nat.le_of_dvd (by omega) hm) hp.out.pos
    have hdiv : (m+p+1)/p-1 = ((m+1)/p-1)+1 := by
      rw [show m+p+1 = (m+1)+p by omega, Nat.add_div_right _ hp.out.pos]
      omega
    have he : (m:ℚ_[p])+1 = (p:ℚ_[p])*(((m+1)/p-1:ℕ):ℚ_[p])+(p:ℚ_[p]) := by
      have hh : m+1 = p*((m+1)/p-1)+p := by
        have ht := Nat.mul_div_cancel' hm
        rw [show (m+1)/p = ((m+1)/p-1)+1 by omega, Nat.mul_add, Nat.mul_one] at ht
        omega
      exact_mod_cast hh
    rw [hdiv, he]
    convert matching_square_step (primeParameter p) (primeParameter_unit hp2).1 Y ((m+1)/p-1) using 1 <;> ring
  · have hm' : ¬p ∣ m+p+1 := fun h => hm ((prime_dvd_step_iff m).mp h)
    rw [dissectedSquare_nonmatching hp2 hp3 Y m hm,
      dissectedSquare_nonmatching hp2 hp3 Y (m+p) hm']
    let d : ℚ := ((m+1:ℕ):ℚ)-(p:ℚ)
    have hd := rational_nonmultiple_sub_prime (m+1) hm
    have h := primeReciprocalG_shift hp2 hp3 d hd.1 hd.2 2 1
    have hshift : d+(p:ℚ)*((1:ℕ):ℚ) = ((m+p+1:ℕ):ℚ)-(p:ℚ) := by
      dsimp [d]
      push_cast
      ring
    simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, one_mul] at h
    have he : (d:ℚ_[p])+(p:ℚ_[p]) = (m:ℚ_[p])+1 := by
      dsimp [d]
      push_cast
      ring
    rw [mul_one, he] at h
    have hz : (primeParameter p:ℚ_[p]) ≠ 0 := by exact_mod_cast (primeParameter_unit hp2).1
    have hh := (eq_div_iff hz).mp h
    have hs := padicReciprocalSeries_congr _ _ hshift
      (rational_unit_add_prime_mul d hd.1 hd.2 1).1
      (rational_unit_add_prime_mul d hd.1 hd.2 1).2
      (rational_nonmultiple_sub_prime (m+p+1) hm').1
      (rational_nonmultiple_sub_prime (m+p+1) hm').2 2
    rw [hs] at hh
    simpa only [d, div_eq_mul_inv, mul_comm] using hh

end
end Li2

end
