module
public import Li2Unified.Modular.Base.ClassBasisAppend
public import Li2Unified.Modular.Base.ClassBasisDegree

set_option backward.privateInPublic true

@[expose] public section

/-! The literal multiplicities and integer product polynomials of the prime-edge basis. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def primeMultiplicity (p : ℕ) (a : Fin p) : ℕ := if a.val < p-3 then 2 else 1

def primeCenter (p : ℕ) (a : Fin p) : ℤ := -(a.val:ℤ)

abbrev PrimeJet (p : ℕ) := (a : Fin p) × Fin (primeMultiplicity p a)

def primeJetPoly (p : ℕ) (a : PrimeJet p) : ℤ[X] :=
  classBasisPoly (primeCenter p) (primeMultiplicity p) a.1 a.2.val

def primeProduct (p : ℕ) : ℤ[X] :=
  fullClassProduct (primeCenter p) (primeMultiplicity p)

theorem primeMultiplicity_sum (p : ℕ) (hp : 3 ≤ p) :
    (∑ a : Fin p, primeMultiplicity p a) = 2*p-3 := by
  unfold primeMultiplicity
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => if a < p-3 then 2 else 1) p]
  have he : p = (p-3)+3 := by omega
  conv_lhs => arg 1; rw [he]
  rw [Finset.sum_range_add]
  have hlow : (∑ a ∈ Finset.range (p-3), if a < p-3 then 2 else 1) = (p-3)*2 := by
    calc
      _ = ∑ a ∈ Finset.range (p-3), (2:ℕ) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [if_pos (Finset.mem_range.mp ha)]
      _ = _ := by simp
  have hhigh : (∑ a ∈ Finset.range 3, if (p-3)+a < p-3 then 2 else 1) = 3 := by
    have hn (a : ℕ) : ¬(p-3)+a < p-3 := by omega
    simp only [if_neg (hn _), Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rw [hlow, hhigh]
  omega

theorem primeJet_card (p : ℕ) (hp : 3 ≤ p) : Fintype.card (PrimeJet p) = 2*p-3 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact primeMultiplicity_sum p hp

theorem primeCenter_mod_injective (p : ℕ) :
    Function.Injective (fun a : Fin p => (primeCenter p a : ZMod p)) := by
  intro a b hab
  apply Fin.ext
  simp only [primeCenter, Int.cast_neg, Int.cast_natCast] at hab
  have hh := congrArg ZMod.val (neg_injective hab)
  simpa only [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hh

theorem primeJetPoly_natDegree_lt (p : ℕ) (hp : 3 ≤ p) (a : PrimeJet p) :
    (primeJetPoly p a).natDegree < 2*p-3 := by
  rw [← primeMultiplicity_sum p hp]
  exact classBasisPoly_natDegree_lt _ _ _ _ a.2.isLt

theorem primeProduct_monic (p : ℕ) : (primeProduct p).Monic :=
  fullClassProduct_monic _ _

theorem primeProduct_natDegree (p : ℕ) (hp : 3 ≤ p) :
    (primeProduct p).natDegree = 2*p-3 := by
  rw [primeProduct, fullClassProduct_natDegree, primeMultiplicity_sum p hp]

end
end Li2

end
