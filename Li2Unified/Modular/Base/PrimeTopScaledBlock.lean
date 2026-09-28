module
public import Li2Unified.Modular.Base.PrimeTopFixedEntry
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The original highest-degree vector is unchanged by the unit normalization. -/
theorem primeTop_block_scaled_GV (hp4 : 3 < p) :
    GV p (primeNormalizedMatrix hp4 (Sum.inr 5) (Sum.inr 5) -
      C ((p:ℚ) * edgeBlock 5 5))
      (primeBlockWeight (p := p) (Sum.inr 5) +
        primeBlockWeight (p := p) (Sum.inr 5) + 1) := by
  unfold primeNormalizedMatrix
  rw [primeBlockUnitScale_top, one_mul, C_1, one_mul]
  unfold primeOriginalNumeratorEntry
  rw [primeBlock_original_basis_top]
  have h := GV_of_cube_padic_leading_bound
    (numeratorFunctional (4*(p-1)) ((D (p-1))^3 *
      (primeProduct p*primeProduct p).map (Int.castRingHom ℚ)))
    (-7609/72) 4 (by
      intro n
      simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using!
        primeTop_fixed_entry_leading hp4 n)
  rw [show edgeBlock 5 5 = (-7609/72:ℚ) from rfl,
    show primeBlockWeight (p := p) (Sum.inr 5) = (1/2:ℚ) from rfl]
  norm_num only [show (1/2:ℚ)+(1/2:ℚ)+1 = 2 by norm_num]
  simpa only [neg_div, show ((4:ℕ):ℤ)-3 = 1 by norm_num, zpow_one,
    show ((4:ℕ):ℚ)-2 = 2 by norm_num] using! h

end
end Li2

end
