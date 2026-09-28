module
public import Li2Unified.Modular.Base.PrimeCubeValuationBridge
public import Li2Unified.Modular.Base.PrimeRemainingCrossBounds

set_option backward.privateInPublic true

@[expose] public section

open Polynomial
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma primeLow_index_margin (hp4 : 3 < p) (a : Fin p)
    (ha : a.val ≤ p-4) (i : Fin (primeMultiplicity p a)) :
    (1/2 : ℚ) ≤ 3/2-(i.val : ℚ) := by
  have hm := primeMultiplicity_low hp4 a ha
  have hi0 := i.isLt
  have hi : i.val ≤ 1 := by omega
  have hiq : (i.val : ℚ) ≤ 1 := by exact_mod_cast hi
  linarith

lemma GV.with_strict_margin {F : ℚ[X]} {w ε : ℚ}
    (h : GV p F (w+ε)) (hε : 0 < ε) :
    GV p F (w+ε) ∧
      ∀ n, F.coeff n = 0 ∨ w < (padicValRat p (F.coeff n) : ℚ) :=
  ⟨h, fun n => h.strict_coeff_of_margin hε n⟩

end
end Li2

end
