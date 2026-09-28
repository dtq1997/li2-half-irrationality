module
public import Li2Unified.Modular.Base.DecayResidue

set_option backward.privateInPublic true

@[expose] public section

/-! the 3-adic bound for the SAME Qtilde n = S_n^(2n)/F_n Q_n.
With L = Nat.log 3 (7n-2) and S3 n = sum_{a<2n} (2a+1-n)^+ (so 4 S3 n + n%2 = 9n^2),
for every n>=1, every coefficient of Qtilde n has v_3 >= -S3 n - 4nL. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

/-- binomGram entries are the literal functional applied to gramNum. -/
lemma binomGram_apply (n : ℕ) (a b : Fin (2*n)) :
    binomGram n a b = numeratorFunctional (4*n) (gramNum n a b) := rfl

def S3 (n : ℕ) : ℕ := ∑ a ∈ Finset.range (2*n), (2*a+1-n)

end
end Li2

end
