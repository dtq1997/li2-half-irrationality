module
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorization.Basic

set_option backward.privateInPublic true

@[expose] public section

namespace Li2

def ratPrimeSupport (s : ℚ) : Finset ℕ :=
  s.num.natAbs.factorization.support ∪ s.den.factorization.support

theorem ratPrimeSupport_prime {s : ℚ} {p : ℕ}
    (hp : p ∈ ratPrimeSupport s) : p.Prime := by
  change p ∈ s.num.natAbs.factorization.support ∪ s.den.factorization.support at hp
  rcases Finset.mem_union.mp hp with hn | hd
  · exact Nat.prime_of_mem_primeFactors (n := s.num.natAbs) (by simpa using hn)
  · exact Nat.prime_of_mem_primeFactors (n := s.den) (by simpa using hd)

theorem padicValRat_eq_factorizations (p : ℕ) (hp : p.Prime) (s : ℚ) :
    padicValRat p s =
      (s.num.natAbs.factorization p : ℤ) - (s.den.factorization p : ℤ) := by
  rw [padicValRat_def]
  change (padicValNat p s.num.natAbs : ℤ) - (padicValNat p s.den : ℤ) = _
  rw [← Nat.factorization_def s.num.natAbs hp,
    ← Nat.factorization_def s.den hp]

theorem padicValRat_eq_zero_of_not_mem_ratPrimeSupport {s : ℚ} {p : ℕ}
    (hp : p.Prime) (hnot : p ∉ ratPrimeSupport s) : padicValRat p s = 0 := by
  change p ∉ s.num.natAbs.factorization.support ∪ s.den.factorization.support at hnot
  have hn : s.num.natAbs.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hnot (Finset.mem_union.mpr (Or.inl h)))
  have hd : s.den.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp (fun h => hnot (Finset.mem_union.mpr (Or.inr h)))
  rw [padicValRat_eq_factorizations p hp s, hn, hd]
  simp

theorem mem_ratPrimeSupport_iff (s : ℚ) (p : ℕ) :
    p ∈ ratPrimeSupport s ↔ p.Prime ∧ padicValRat p s ≠ 0 := by
  constructor
  · intro hp
    have hprime := ratPrimeSupport_prime hp
    refine ⟨hprime, ?_⟩
    intro hzero
    rw [padicValRat_eq_factorizations p hprime s] at hzero
    have heq : s.num.natAbs.factorization p = s.den.factorization p :=
      Int.ofNat_inj.mp (sub_eq_zero.mp hzero)
    change p ∈ s.num.natAbs.factorization.support ∪ s.den.factorization.support at hp
    have hn : s.num.natAbs.factorization p ≠ 0 := by
      rcases Finset.mem_union.mp hp with hn | hd
      · exact Finsupp.mem_support_iff.mp hn
      · rw [heq]
        exact Finsupp.mem_support_iff.mp hd
    have hd : s.den.factorization p ≠ 0 := by
      rw [← heq]
      exact hn
    have hdiv : p ∣ Nat.gcd s.num.natAbs s.den :=
      Nat.dvd_gcd (Nat.dvd_of_factorization_pos hn) (Nat.dvd_of_factorization_pos hd)
    have hone : p ∣ 1 := by
      simpa only [s.reduced.gcd_eq_one] using hdiv
    exact hprime.ne_one (Nat.dvd_one.mp hone)
  · rintro ⟨hp, hv⟩
    by_contra hnot
    exact hv (padicValRat_eq_zero_of_not_mem_ratPrimeSupport hp hnot)

theorem finite_prime_padicValRat_support (s : ℚ) :
    {p : ℕ | p.Prime ∧ padicValRat p s ≠ 0}.Finite := by
  apply (ratPrimeSupport s).finite_toSet.subset
  intro p hp
  exact (mem_ratPrimeSupport_iff s p).mpr hp

end Li2

end
