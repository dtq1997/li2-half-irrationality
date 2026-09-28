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

end
end Li2

end
