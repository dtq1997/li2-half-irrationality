module
public import Li2Unified.Modular.Base.RestrictedApproximation
public import Li2Unified.Modular.Base.MomentSequenceShift

set_option backward.privateInPublic true

@[expose] public section

/-! The bounded shift identity follows from the exact polynomial identity and
the uniform truncation estimates, for every nonnegative integer shift. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def restrictedEval (x : ℤ_[p]) (f : PowerSeries ℤ_[p]) : ℤ_[p] :=
  restrictedMoment (fun n => x^n) f

lemma restrictedEval_polynomial (x : ℤ_[p]) (P : (ℤ_[p])[X]) :
    restrictedEval x (P : PowerSeries ℤ_[p]) = P.eval x := by
  rw [restrictedEval, restrictedMoment_polynomial, eval_eq_sum]

theorem restrictedMoment_shift_scaled (μ : ℕ → ℤ_[p]) (z : ℤ_[p])
    (hrec : ∀ k, μ k = z+z*∑ j ∈ Finset.range (k+1), (Nat.choose k j : ℤ_[p])*μ j)
    (f : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f) (k : ℕ) :
    z^k*restrictedMoment μ (restrictedTranslate (k:ℤ_[p]) f) = restrictedMoment μ f-
      ∑ j ∈ Finset.range k, z^(j+1)*restrictedEval ((j:ℤ_[p])+1) f := by
  have hl : Tendsto (fun N => z^k*restrictedMoment μ
      (restrictedTranslate (k:ℤ_[p]) (PowerSeries.trunc N f : PowerSeries ℤ_[p])))
      atTop (𝓝 (z^k*restrictedMoment μ (restrictedTranslate (k:ℤ_[p]) f))) :=
    tendsto_const_nhds.mul (translatedMoment_trunc_tendsto μ (k:ℤ_[p]) f hf)
  have hsum : Tendsto (fun N => ∑ j ∈ Finset.range k,
      z^(j+1)*restrictedEval ((j:ℤ_[p])+1) (PowerSeries.trunc N f : PowerSeries ℤ_[p]))
      atTop (𝓝 (∑ j ∈ Finset.range k, z^(j+1)*restrictedEval ((j:ℤ_[p])+1) f)) := by
    apply tendsto_finset_sum
    intro j _
    exact tendsto_const_nhds.mul
      (restrictedMoment_trunc_tendsto (fun n => ((j:ℤ_[p])+1)^n) f hf)
  have hr := (restrictedMoment_trunc_tendsto μ f hf).sub hsum
  have he (N : ℕ) : z^k*restrictedMoment μ
      (restrictedTranslate (k:ℤ_[p]) (PowerSeries.trunc N f : PowerSeries ℤ_[p])) =
      restrictedMoment μ (PowerSeries.trunc N f : PowerSeries ℤ_[p])-
      ∑ j ∈ Finset.range k, z^(j+1)*restrictedEval ((j:ℤ_[p])+1)
        (PowerSeries.trunc N f : PowerSeries ℤ_[p]) := by
    simp only [restrictedTranslate_polynomial, restrictedMoment_polynomial, restrictedEval_polynomial]
    exact sequenceG_shift_scaled μ z hrec (PowerSeries.trunc N f) k
  exact tendsto_nhds_unique hl (hr.congr' (Filter.Eventually.of_forall fun N => (he N).symm))

end
end Li2

end
