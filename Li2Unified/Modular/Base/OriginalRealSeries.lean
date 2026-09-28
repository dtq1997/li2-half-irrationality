module
public import Li2Unified.Modular.Base.OriginalPartialFractions
public import Li2Unified.Modular.Base.MomentFunctional
public import Li2Unified.Modular.Base.PoleIdentity

set_option backward.privateInPublic true

@[expose] public section

/-! Real derivative expansion of the actual quotient and residues. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def originalPoleDerivativeTerm (j k : ℕ) : ℝ :=
  (-1/2:ℝ)^(k+1) * (j:ℝ) / ((k+j:ℕ)+1:ℝ)^2

lemma summable_originalPoleDerivativeTerm (j : ℕ) :
    Summable (originalPoleDerivativeTerm j) := by
  have hg : Summable (fun k : ℕ => (1/2:ℝ)^(k+1)) := by
    simpa only [pow_succ, one_div] using
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).mul_right (1/2:ℝ)
  have hb : Summable (fun k : ℕ =>
      |(-1/2:ℝ)^(k+1) / ((k+j:ℕ)+1:ℝ)^2|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _ hg
    intro k
    rw [abs_div, abs_pow, abs_pow]
    norm_num
    have hk : (0:ℝ) ≤ (k+j:ℕ) := Nat.cast_nonneg _
    have hd : (1:ℝ) ≤ ((k+j:ℕ)+1:ℝ)^2 := by nlinarith
    exact div_le_self (by positivity) (by simpa only [Nat.cast_add] using hd)
  have h := (summable_abs_iff.mp hb).mul_right (j:ℝ)
  convert h using 1
  funext k
  unfold originalPoleDerivativeTerm
  ring

def originalRealDerivativeExpansion (m : ℕ) (F : ℚ[X]) (x : ℝ) : ℝ :=
  polynomialIntegrand (F /ₘ D m) x +
    ∑ j ∈ Finset.Icc 1 m,
      (originalResidue m F j:ℝ) * (j:ℝ) / (x+(j:ℝ))^2

lemma originalRealDerivativeExpansion_term (m : ℕ) (F : ℚ[X]) (k : ℕ) :
    (-1/2:ℝ)^(k+1) * originalRealDerivativeExpansion m F ((k:ℝ)+1) =
      (-1/2:ℝ)^(k+1) * polynomialIntegrand (F /ₘ D m) ((k:ℝ)+1) +
      ∑ j ∈ Finset.Icc 1 m,
        (originalResidue m F j:ℝ)*originalPoleDerivativeTerm j k := by
  unfold originalRealDerivativeExpansion
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold originalPoleDerivativeTerm
  push_cast
  ring

theorem summable_originalRealDerivativeExpansion (m : ℕ) (F : ℚ[X]) :
    Summable (fun k : ℕ => (-1/2:ℝ)^(k+1) *
      originalRealDerivativeExpansion m F ((k:ℝ)+1)) := by
  simp_rw [originalRealDerivativeExpansion_term]
  apply (summable_polynomialIntegrand (F /ₘ D m)).add
  apply summable_sum
  intro j _
  exact (summable_originalPoleDerivativeTerm j).mul_left _

theorem numeratorFunctional_real_series (m : ℕ) (F : ℚ[X]) :
    (numeratorFunctional m F).eval₂ (Rat.castHom ℝ) li2NegHalf =
      ∑' k : ℕ, (-1/2:ℝ)^(k+1) *
        originalRealDerivativeExpansion m F ((k:ℝ)+1) := by
  have hp := summable_polynomialIntegrand (F /ₘ D m)
  have hs (j : ℕ) : Summable (fun k : ℕ =>
      (originalResidue m F j:ℝ)*originalPoleDerivativeTerm j k) :=
    (summable_originalPoleDerivativeTerm j).mul_left _
  have hsum : Summable (fun k : ℕ => ∑ j ∈ Finset.Icc 1 m,
      (originalResidue m F j:ℝ)*originalPoleDerivativeTerm j k) := by
    apply summable_sum
    intro j _
    exact hs j
  simp_rw [originalRealDerivativeExpansion_term]
  rw [hp.tsum_add hsum, Summable.tsum_finsetSum]
  · rw [← polynomialMoment_series]
    simp_rw [tsum_mul_left, originalPoleDerivativeTerm, pole_functional_identity]
    simp only [numeratorFunctional, originalResidue, eval₂_add, eval₂_C,
      eval₂_finset_sum, eval₂_mul, eval₂_sub, eval₂_X, Rat.coe_castHom,
      Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  · intro j _
    exact hs j

end
end Li2

end
