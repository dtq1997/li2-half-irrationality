module
public import Li2Unified.Modular.Base.OriginalContourPatched

set_option backward.privateInPublic true

@[expose] public section

open Polynomial MeasureTheory
open scoped BigOperators
namespace Li2
noncomputable section

lemma boundaryIntegral_congr_four_edges (f g : ℂ → ℂ) (a b : ℂ)
    (hb : ∀ x : ℝ, f (x + a.im * Complex.I) = g (x + a.im * Complex.I))
    (ht : ∀ x : ℝ, f (x + b.im * Complex.I) = g (x + b.im * Complex.I))
    (hr : ∀ y : ℝ, f (b.re + y * Complex.I) = g (b.re + y * Complex.I))
    (hl : ∀ y : ℝ, f (a.re + y * Complex.I) = g (a.re + y * Complex.I)) :
    Complex.boundaryIntegral f a b = Complex.boundaryIntegral g a b := by
  unfold Complex.boundaryIntegral
  rw [funext hb, funext ht, funext hr, funext hl]

end
end Li2

end
