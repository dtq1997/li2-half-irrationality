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

end
end Li2

end
