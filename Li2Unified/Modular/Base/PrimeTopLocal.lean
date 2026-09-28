module
public import Li2Unified.Modular.Base.PrimeHighEntry

set_option backward.privateInPublic true

@[expose] public section

/-! All local contributions to the original highest-degree self-pairing.
The zero disc and all three high discs contribute at the same order. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

theorem fieldPolynomial_prime_power_bound (F : (ℚ_[p])[X]) (k m : ℕ)
    (hF : ∀ n, ‖F.coeff n‖ ≤ ‖(p:ℚ_[p])‖^m) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^k)*F).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(k+m) := by
  rw [coeff_C_mul,norm_mul,norm_pow,pow_add]
  exact mul_le_mul_of_nonneg_left (hF n) (by positivity)

def primeTopDiscLeading (a : Fin p) : ℚ_[p] :=
  (primeLocalUnit p a:ℚ_[p])^2 *
    (if a.val = 0 then (primeDiscUnitConstant a.val a.isLt:ℚ_[p]) * ((-17773/36:ℚ):ℚ_[p])
    else if a.val ≤ p-4 then 0
    else -(a.val:ℚ_[p]) * (primeDiscUnitConstant a.val a.isLt:ℚ_[p]) * ((266/9:ℚ):ℚ_[p]))

theorem primeTop_zero_leading (hp4 : 3 < p) (n : ℕ) :
    let a : Fin p := ⟨0,by omega⟩
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*primeTopDiscLeading a)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  dsimp only
  let a : Fin p := ⟨0,by omega⟩
  have hm : primeMultiplicity p a = 2 := primeMultiplicity_low hp4 a (by simp [a])
  have ht : ∃ E : ℤ[X], (primeProduct p*primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^4)*X^4*(C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E) := by
    simpa only [hm] using! primeProduct_square_expansion p a
  have h := primeDiscTest_zero_U_leading hp4 (primeProduct p*primeProduct p) 4 ⟨4,by decide⟩
    (primeLocalUnit p a*primeLocalUnit p a) (primeEta (p := p) (by omega) (by omega)) ht n
  rw [primeDiscContribution_cube_zero]
  simpa [primeTopDiscLeading,a,PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,
    PadicInt.coe_natCast,pow_two,mul_assoc] using! h

theorem primeTop_high_leading (hp4 : 3 < p) (a : Fin p) (ha : p-4 < a.val) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*primeTopDiscLeading a)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  have hm : primeMultiplicity p a = 1 := by unfold primeMultiplicity; rw [if_neg (by omega)]
  have ht : ∃ E : ℤ[X], (primeProduct p*primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^2)*X^2*(C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E) := by
    simpa only [hm] using! primeProduct_square_expansion p a
  have h : ∀ l, ‖(C (p:ℚ_[p])*primeDiscContribution hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^2*primeTopDiscLeading a)).coeff l‖ ≤ ‖(p:ℚ_[p])‖^3 := by
    intro l
    rw [primeDiscContribution_linear_high hp4 a ha]
    have h := primeDiscTest_high_scaled_leading hp4 (primeProduct p*primeProduct p) a ha
      2 ⟨2,by decide⟩ (primeLocalUnit p a*primeLocalUnit p a)
      (primeEta (p := p) (by omega) (by omega)) ht l
    have ha0 : a ≠ 0 := by
      intro he
      have hz : a.val = 0 := by simp [he]
      omega
    simpa [primeTopDiscLeading,ha0,if_neg (by omega : a.val ≠ 0),if_neg (by omega : ¬ a.val ≤ p-4),
      PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_intCast,PadicInt.coe_natCast,pow_two,mul_assoc] using! h
  have he : C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*primeTopDiscLeading a) =
      C ((p:ℚ_[p])^2)*(C (p:ℚ_[p])*primeDiscContribution hp4 a (primeProduct p*primeProduct p) -
        C ((p:ℚ_[p])^2*primeTopDiscLeading a)) := by
    simp only [C_mul,C_pow]
    ring
  rw [he]
  exact fieldPolynomial_prime_power_bound _ 2 3 h n

theorem primeTop_low_bound (hp4 : 3 < p) (a : Fin p) (ha0 : 0 < a.val)
    (ha : a.val ≤ p-4) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^5 := by
  have hm : primeMultiplicity p a = 2 := primeMultiplicity_low hp4 a ha
  obtain ⟨E,hE⟩ := primeProduct_square_expansion p a
  have ht : ∃ F : ℤ[X], (primeProduct p*primeProduct p).comp (primeDiscSubstitution p a) =
      C ((p:ℤ)^4)*F := by
    refine ⟨X^4*(C (primeLocalUnit p a*primeLocalUnit p a)+C (p:ℤ)*E),?_⟩
    simpa only [hm,mul_assoc] using! hE
  have h : ∀ l, ‖(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a (primeProduct p*primeProduct p)).coeff l‖ ≤
      ‖(p:ℚ_[p])‖^4 := by
    intro l
    rw [primeDiscContribution_scaled_low hp4 a ha0 ha]
    simpa only [coeff_map,norm_pow] using! primeDiscTestScaled_factor_bound hp4 _ a 4
      (primeEta (p := p) (by omega) (by omega)) ht l
  have he : C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p) =
      C ((p:ℚ_[p])^1)*(C ((p:ℚ_[p])^2)*primeDiscContribution hp4 a (primeProduct p*primeProduct p)) := by
    simp only [C_pow]
    ring
  rw [he]
  exact fieldPolynomial_prime_power_bound _ 1 4 h n

theorem primeTop_disc_leading (hp4 : 3 < p) (a : Fin p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*primeDiscContribution hp4 a (primeProduct p*primeProduct p) -
      C ((p:ℚ_[p])^4*primeTopDiscLeading a)).coeff n‖ ≤ ‖(p:ℚ_[p])‖^5 := by
  by_cases hz : a.val = 0
  · have he : a = (⟨0,by omega⟩:Fin p) := Fin.ext hz
    rw [he]
    exact primeTop_zero_leading hp4 n
  · by_cases hl : a.val ≤ p-4
    · simpa only [primeTopDiscLeading,if_neg hz,if_pos hl,mul_zero,C_0,sub_zero] using!
        primeTop_low_bound hp4 a (by omega) hl n
    · exact primeTop_high_leading hp4 a (by omega) n

end
end Li2

end
