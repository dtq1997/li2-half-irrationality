module
public import Li2Unified.Modular.Base.PrimeNormalizedCrossBlock
public import Li2Unified.Modular.Base.PrimeLowScaledBlock
public import Li2Unified.Modular.Base.PrimeTopEntry
public import Li2Unified.Modular.Base.PrimeEdgeNormValues
public import Li2Unified.Modular.Base.PrimeZeroRationalLeading
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix
public import Li2Unified.Modular.Base.PrimeLowWeightUnit
public import Mathlib.LinearAlgebra.Matrix.Block

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Integer row powers; the edge half-power is placed in the column factor. -/
def primeReferenceRowExponent : PrimeBlockIndex p → ℤ
  | Sum.inl ai => (ai.2.val:ℤ)-1
  | Sum.inr k => primeEdgeIntegerWeight k

def primeReferenceColExponent : PrimeBlockIndex p → ℤ
  | Sum.inl ai => (ai.2.val:ℤ)-1
  | Sum.inr k => primeEdgeIntegerWeight k+1

lemma primeReference_exponent_sum (hp4 : 3 < p) :
    (∑ x : PrimeBlockIndex p, primeReferenceRowExponent x) +
      (∑ x : PrimeBlockIndex p, primeReferenceColExponent x) =
      -2*((p-1:ℕ):ℤ) := by
  have hlow :
      (∑ ai : Fin (p-4) × Fin 2,
        (primeReferenceRowExponent (Sum.inl ai)+primeReferenceColExponent (Sum.inl ai))) =
        -2*((p-4:ℕ):ℤ) := by
    rw [Fintype.sum_prod_type]
    simp [primeReferenceRowExponent,primeReferenceColExponent,Fin.sum_univ_two] <;> ring
  have hedge :
      (∑ k : Fin 6, (primeReferenceRowExponent (p := p) (Sum.inr k) +
        primeReferenceColExponent (p := p) (Sum.inr k))) = -6 := by
    norm_num [primeReferenceRowExponent,primeReferenceColExponent,
      primeEdgeIntegerWeight,Fin.sum_univ_succ]
  rw [← Finset.sum_add_distrib,Fintype.sum_sum_type,hlow,hedge]
  have h4 : ((p-4:ℕ):ℤ) = (p:ℤ)-4 := Nat.cast_sub (by omega)
  have h1 : ((p-1:ℕ):ℤ) = (p:ℤ)-1 := Nat.cast_sub (by omega)
  rw [h4,h1]
  ring

lemma primeReference_prod_zpow {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (e : ι → ℤ) :
    (∏ x ∈ S, (p:ℚ)^(e x)) = (p:ℚ)^(∑ x ∈ S, e x) := by
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,ih,zpow_add₀ hpq]

end
end Li2

end
