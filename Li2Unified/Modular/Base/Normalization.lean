module
public import Li2Unified.Modular.Base.Family

set_option backward.privateInPublic true

@[expose] public section

/-! Relate the chosen primitive polynomial to the literal rational determinant.
The scalar may have either sign; all current decay and nonzero statements are
sign-invariant. The zero polynomial is explicitly sent to zero. -/
open Polynomial
namespace Li2

noncomputable section

theorem primitiveQ_proportional (n : ℕ) :
    ∃ a : ℚ, a ≠ 0 ∧ (primitiveQ n).map (algebraMap ℤ ℚ) = C a * Q n := by
  by_cases hn : Q n = 0
  · exact ⟨1, one_ne_zero, by simp [primitiveQ, hn]⟩
  let R := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q n)
  have hR : R ≠ 0 := fun hz => hn (IsFractionRing.integerNormalization_eq_zero_iff.mp hz)
  have hcont : R.content ≠ 0 := fun hz => hR (Polynomial.content_eq_zero_iff.mp hz)
  have hcontQ : (R.content : ℚ) ≠ 0 := by exact_mod_cast hcont
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Q n)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  refine ⟨(b : ℚ)/(R.content : ℚ), div_ne_zero hbQ hcontQ, ?_⟩
  apply Polynomial.ext
  intro k
  have hfac := congrArg (fun f : ℤ[X] => (f.map (algebraMap ℤ ℚ)).coeff k)
    R.eq_C_content_mul_primPart
  have hco : (b : ℚ) * (Q n).coeff k = (R.content : ℚ) * (R.primPart.coeff k : ℚ) := by
    rw [show R.map (algebraMap ℤ ℚ) = b • Q n from hmap] at hfac
    simpa using hfac
  simp only [primitiveQ, if_neg hn, coeff_map, coeff_C_mul]
  change (R.primPart.coeff k : ℚ) = (b : ℚ)/(R.content : ℚ) * (Q n).coeff k
  apply (mul_left_cancel₀ hcontQ)
  field_simp
  nlinarith [hco]

end
end Li2

end
