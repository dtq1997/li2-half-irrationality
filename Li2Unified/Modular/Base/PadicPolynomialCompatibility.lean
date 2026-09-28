module
public import Li2Unified.Modular.Base.ParameterDifferentialDissection
public import Li2Unified.Modular.Base.PrimePoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! Compatibility for any integral p-adic polynomial representing a rational
polynomial. This is not restricted to integer coefficients. -/
open Polynomial
namespace Li2
noncomputable section

lemma sequenceG_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (μ : ℕ → R) (P : R[X]) :
    sequenceG (fun n => φ (μ n)) (P.map φ) = φ (sequenceG μ P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.map_add, sequenceG_add, map_add, hP, hQ]
  | monomial n a => simp [sequenceG, Polynomial.sum_monomial_index]

variable {p : ℕ} [Fact p.Prime]

end
end Li2

end
