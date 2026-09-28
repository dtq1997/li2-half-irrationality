module
public import Li2Unified.Modular.Base.RationalPrimeSupport
public import Mathlib.Algebra.Polynomial.Basic

set_option backward.privateInPublic true

@[expose] public section

namespace Li2
open Polynomial
noncomputable section

def ratPolynomialPrimeSupport (F : ℚ[X]) : Finset ℕ :=
  F.support.biUnion (fun n => ratPrimeSupport (F.coeff n))

theorem mem_ratPolynomialPrimeSupport_iff (F : ℚ[X]) (p : ℕ) :
    p ∈ ratPolynomialPrimeSupport F ↔
      p.Prime ∧ ∃ n, padicValRat p (F.coeff n) ≠ 0 := by
  simp only [ratPolynomialPrimeSupport, Finset.mem_biUnion]
  constructor
  · rintro ⟨n, _, hn⟩
    obtain ⟨hp, hv⟩ := (mem_ratPrimeSupport_iff (F.coeff n) p).mp hn
    exact ⟨hp, n, hv⟩
  · rintro ⟨hp, n, hv⟩
    refine ⟨n, Polynomial.mem_support_iff.mpr ?_,
      (mem_ratPrimeSupport_iff (F.coeff n) p).mpr ⟨hp,hv⟩⟩
    intro hz
    exact hv (by rw [hz, padicValRat.zero])

theorem padicValRat_coeff_eq_zero_of_not_mem_ratPolynomialPrimeSupport
    (F : ℚ[X]) {p : ℕ} (hp : p.Prime) (hn : p ∉ ratPolynomialPrimeSupport F)
    (n : ℕ) : padicValRat p (F.coeff n) = 0 := by
  by_contra hv
  exact hn ((mem_ratPolynomialPrimeSupport_iff F p).mpr ⟨hp,n,hv⟩)

theorem finite_prime_polynomial_valuation_support (F : ℚ[X]) :
    {p : ℕ | p.Prime ∧ ∃ n, padicValRat p (F.coeff n) ≠ 0}.Finite := by
  apply (ratPolynomialPrimeSupport F).finite_toSet.subset
  intro p hp
  exact (mem_ratPolynomialPrimeSupport_iff F p).mpr hp

end
end Li2

end
