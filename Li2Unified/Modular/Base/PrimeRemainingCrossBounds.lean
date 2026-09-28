module
public import Li2Unified.Modular.Base.PrimeCrossDiscBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Zero/high and distinct-high pairs are zero entries inside the
six-dimensional augmented block. Low/zero and low/high cross distinct blocks. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma primeDistinctJet_cube_order (hp4 : 3 < p) (a b : PrimeJet p)
    (hab : a.1 ≠ b.1) (k : ℕ)
    (ha : k ≤ a.2.val+primeMultiplicity p a.1+primeDiscCubeGain a.1)
    (hb : k ≤ b.2.val+primeMultiplicity p b.1+primeDiscCubeGain b.1)
    (hk : k ≤ 4) (c : Fin p) :
    k ≤ primeJetLocalOrder p a c+primeJetLocalOrder p b c+primeDiscCubeGain c := by
  by_cases hca : c = a.1
  · subst c
    simpa only [primeJetLocalOrder,ite_true,if_pos rfl,if_neg hab] using! ha
  · by_cases hcb : c = b.1
    · subst c
      simpa only [primeJetLocalOrder,ite_true,if_neg (Ne.symm hab),if_pos rfl,
        Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using! hb
    · simp only [primeJetLocalOrder,ite_true,if_neg hca,if_neg hcb]
      apply hk.trans
      by_cases hz : c.val = 0
      · have hm : primeMultiplicity p c = 2 := primeMultiplicity_low hp4 c (by omega)
        simp only [hm,primeDiscCubeGain,if_pos hz] <;> omega
      · by_cases hl : c.val ≤ p-4
        · simp only [primeMultiplicity_low hp4 c hl,primeDiscCubeGain,if_neg hz,if_pos hl] <;> omega
        · have hm : primeMultiplicity p c = 1 := by
            unfold primeMultiplicity
            rw [if_neg (by omega)]
          simp only [hm,primeDiscCubeGain,if_neg hz,if_neg hl] <;> omega

end
end Li2

end
