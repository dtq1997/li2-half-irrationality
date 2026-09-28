module
public import Li2Unified.Modular.Base.PrimeStrictInterval

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology
namespace Li2.PrimeSums
noncomputable section

theorem sum_mixed_affine_nat_tendsto {ι : Type*} (s : Finset ι)
    (strict : ι → Bool) (α β a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i < b i) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ s, if strict i then
        affineOpenSum (α i) (β i) (a i) (b i) (n : ℝ)
      else affineSum (α i) (β i) (a i) (b i) (n : ℝ))/(n : ℝ)^2)
      atTop (𝓝 (∑ i ∈ s, (α i*((b i^2-a i^2)/2)+β i*(b i-a i)))) := by
  simp_rw [Finset.sum_div]
  refine tendsto_finset_sum s ?_
  intro i hi
  cases hstrict : strict i with
  | false =>
      simpa only [hstrict, Bool.false_eq_true, ↓reduceIte] using
        affineSum_nat_tendsto (α i) (β i) (ha i hi) (hab i hi).le
  | true =>
      simpa only [hstrict, ↓reduceIte] using
        affineOpenSum_nat_tendsto (α i) (β i) (ha i hi) (hab i hi)

end
end Li2.PrimeSums

end
