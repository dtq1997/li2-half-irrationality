module
public import Li2Unified.Modular.Base.ReciprocalFunctional
public import Li2Unified.Modular.Base.PoleDissectionWindow

set_option backward.privateInPublic true

@[expose] public section

/-! The square-denominator terms are constructed separately on matching
simple poles and nonmatching restricted series. No dissection identity is
used in their definition. The index m represents the denominator pu+m+1-p. -/
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma rational_nonmultiple_sub_prime (n : ℕ) (hn : ¬p ∣ n) :
    (n:ℚ)-(p:ℚ) ≠ 0 ∧ padicValRat p ((n:ℚ)-(p:ℚ)) = 0 := by
  have hi : ¬(p:ℤ) ∣ (n:ℤ)-(p:ℤ) := by
    intro h
    have hh : (p:ℤ) ∣ (n:ℤ) := by simpa using dvd_add h (dvd_refl (p:ℤ))
    exact hn (by exact_mod_cast hh)
  have hne : (n:ℤ)-(p:ℤ) ≠ 0 := fun h => hi (h ▸ dvd_zero _)
  constructor
  · exact_mod_cast hne
  · have h := padicValInt.eq_zero_of_not_dvd hi
    have hh : padicValRat p (((n:ℤ)-(p:ℤ):ℤ):ℚ) = 0 := by
      rw [padicValRat.of_int, h]
      rfl
    simpa only [Int.cast_sub, Int.cast_natCast] using hh

lemma padicReciprocalSeries_congr (d d' : ℚ) (he : d = d')
    (hd : d ≠ 0) (hv : padicValRat p d = 0)
    (hd' : d' ≠ 0) (hv' : padicValRat p d' = 0) (e : ℕ) :
    padicReciprocalSeries d hd hv e = padicReciprocalSeries d' hd' hv' e := by
  subst d'
  rfl

end
end Li2

end
