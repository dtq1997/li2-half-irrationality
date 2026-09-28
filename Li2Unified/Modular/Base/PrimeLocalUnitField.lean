module
public import Li2Unified.Modular.Base.PrimeHighWeights
public import Li2Unified.Modular.Base.PrimeJets

set_option backward.privateInPublic true

@[expose] public section

/-! Reduction of the actual product-basis units. Each full simple-factor
product is -1; doubling the low multiplicities leaves the reciprocal tail. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma primeFieldUnitFactor_range (a : Fin p) :
    (∏ b ∈ Finset.range p,primeFieldUnitFactor (p := p) a.val b) = -1 := by
  have hs : Finset.Ico 1 p = Finset.Icc 1 (p-1) := by
    ext j
    simp only [Finset.mem_Ico,Finset.mem_Icc]
    have := hp.out.pos
    omega
  rw [Finset.prod_range_eq_mul_Ico _ hp.out.pos,hs]
  change primeFieldUnitFactor a.val 0 * primeFieldUnitProduct a.val (p-1) = -1
  have he := primeFieldUnitProduct_succ (p := p) a.val (p-1)
  rw [Nat.sub_add_cancel hp.out.pos,primeFieldUnitProduct_full_period a.val a.isLt] at he
  have hf : primeFieldUnitFactor (p := p) a.val p = primeFieldUnitFactor a.val 0 := by
    simpa using primeFieldUnitFactor_period (p := p) a.val 0
  rw [hf] at he
  simpa only [mul_comm] using he.symm

lemma primeLocalUnit_field_product (a : Fin p) :
    (primeLocalUnit p a:ZMod p) = ∏ b ∈ Finset.range p,
      (primeFieldUnitFactor a.val b)^(if b < p-3 then 2 else 1) := by
  have he : (primeLocalUnit p a:ZMod p) =
      ∏ b ∈ Finset.univ.erase a, ((b.val:ZMod p)-(a.val:ZMod p))^(primeMultiplicity p b) := by
    simp only [primeLocalUnit,classProduct,eval_prod,eval_pow,eval_sub,eval_X,eval_C,
      Int.cast_prod,Int.cast_pow,Int.cast_sub,primeCenter,Int.cast_neg,Int.cast_natCast,sub_neg_eq_add]
    apply Finset.prod_congr rfl
    intro b _
    congr 1
    push_cast
    ring
  rw [he]
  calc
    _ = ∏ b ∈ Finset.univ.erase a,(primeFieldUnitFactor (p := p) a.val b.val)^(primeMultiplicity p b) := by
      apply Finset.prod_congr rfl
      intro b hb
      have hba : b.val ≠ a.val := fun h => (Finset.mem_erase.mp hb).1 (Fin.ext h)
      simp only [primeFieldUnitFactor,Nat.mod_eq_of_lt b.isLt,if_pos hba]
    _ = ∏ b : Fin p,(primeFieldUnitFactor (p := p) a.val b.val)^(primeMultiplicity p b) := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
      simp [primeFieldUnitFactor,Nat.mod_eq_of_lt a.isLt]
    _ = _ := by
      unfold primeMultiplicity
      exact Fin.prod_univ_eq_prod_range (fun b : ℕ =>
        (primeFieldUnitFactor (p := p) a.val b)^(if b < p-3 then 2 else 1)) p

def primeFieldUnitTail (a : Fin p) : ZMod p :=
  primeFieldUnitFactor a.val (p-3)*primeFieldUnitFactor a.val (p-2)*primeFieldUnitFactor a.val (p-1)

theorem primeLocalUnit_mul_tail (hp4 : 3 < p) (a : Fin p) :
    (primeLocalUnit p a:ZMod p)*primeFieldUnitTail a = 1 := by
  let f : ℕ → ZMod p := primeFieldUnitFactor a.val
  let L : ZMod p := ∏ b ∈ Finset.range (p-3),f b
  have hs : p = (p-3)+3 := by omega
  have hT : (∏ b ∈ Finset.range 3,f ((p-3)+b)) = primeFieldUnitTail a := by
    norm_num [Finset.prod_range_succ,primeFieldUnitTail,f,
      show p-3+1 = p-2 by omega,show p-3+2 = p-1 by omega]
  have hS : L*primeFieldUnitTail a = -1 := by
    have h := primeFieldUnitFactor_range a
    change (∏ b ∈ Finset.range p,f b) = -1 at h
    conv_lhs at h => arg 1; rw [hs]
    rw [Finset.prod_range_add,hT] at h
    exact h
  have hlow : (∏ b ∈ Finset.range (p-3),f b^(if b < p-3 then 2 else 1)) = L^2 := by
    dsimp only [L]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro b hb
    rw [if_pos (Finset.mem_range.mp hb)]
  have hhigh : (∏ b ∈ Finset.range 3,f ((p-3)+b)^(if (p-3)+b < p-3 then 2 else 1)) =
      primeFieldUnitTail a := by
    have hn (b : ℕ) : ¬ (p-3)+b < p-3 := by omega
    simp only [if_neg (hn _),pow_one]
    exact hT
  rw [primeLocalUnit_field_product]
  change (∏ b ∈ Finset.range p,f b^(if b < p-3 then 2 else 1))*primeFieldUnitTail a = 1
  conv_lhs => arg 1; arg 1; rw [hs]
  rw [Finset.prod_range_add,hlow,hhigh]
  calc
    _ = (L*primeFieldUnitTail a)^2 := by ring
    _ = 1 := by rw [hS]; ring

end
end Li2

end
