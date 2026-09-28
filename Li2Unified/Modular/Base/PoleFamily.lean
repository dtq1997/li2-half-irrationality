module
public import Li2Unified.Modular.Base.Family
public import Li2Unified.Modular.Base.SimplePoles

set_option backward.privateInPublic true

@[expose] public section

/-! Connect generic simple-pole interpolation to the literal Li2 family. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def negativePoles (m : ℕ) : Finset ℤ :=
  (Finset.Icc 1 m).image (fun j : ℕ => -(j : ℤ))

lemma negative_nat_injective : Function.Injective (fun j : ℕ => -(j : ℤ)) := by
  intro a b h
  have he : (a:ℤ) = (b:ℤ) := neg_injective h
  exact_mod_cast he

lemma negativePoles_product (m : ℕ) : SimplePoles.piPl (negativePoles m) = D m := by
  unfold SimplePoles.piPl negativePoles D
  rw [Finset.prod_image]
  · simp only [Int.cast_neg, Int.cast_natCast, C_neg, sub_neg_eq_add]
  · intro a _ b _ h
    exact negative_nat_injective h

lemma D_monic (m : ℕ) : (D m).Monic := by
  rw [← negativePoles_product]
  exact SimplePoles.piPl_monic _

lemma generic_polynomialPart (n k : ℕ) :
    SimplePoles.polyPart (numerator n k) (negativePoles (4*n)) = polynomialPart n k := by
  simp only [SimplePoles.polyPart, negativePoles_product, polynomialPart]

lemma generic_residue (n k j : ℕ) :
    SimplePoles.resP (numerator n k) (negativePoles (4*n)) (-(j:ℤ)) = residue n k j := by
  unfold SimplePoles.resP residue negativePoles
  rw [← Finset.image_erase negative_nat_injective, Finset.prod_image]
  · simp only [Int.cast_neg, Int.cast_natCast, neg_sub_neg]
  · intro a _ b _ h
    exact negative_nat_injective h

theorem numerator_partial_fractions (n k : ℕ) :
    numerator n k = polynomialPart n k * D (4*n) +
      ∑ j ∈ Finset.Icc 1 (4*n), C (residue n k j) *
        ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (X + C (l:ℚ)) := by
  have h := SimplePoles.partial_fractionsP (numerator n k) (negativePoles (4*n))
  rw [generic_polynomialPart, negativePoles_product] at h
  rw [h]
  congr 1
  unfold negativePoles
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    rw [show SimplePoles.resP (numerator n k)
      ((Finset.Icc 1 (4*n)).image (fun j:ℕ => -(j:ℤ))) (-(j:ℤ)) = residue n k j
        from generic_residue n k j]
    rw [← Finset.image_erase negative_nat_injective, Finset.prod_image]
    · simp only [Int.cast_neg, Int.cast_natCast, C_neg, sub_neg_eq_add]
    · intro a _ b _ he
      exact negative_nat_injective he
  · intro a _ b _ he
    exact negative_nat_injective he

end
end Li2

end
