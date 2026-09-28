module
public import Li2Unified.Modular.Base.RestrictedAffineInverse
public import Li2Unified.Modular.Base.RestrictedPoleBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Uniform coefficient error bounds for finite products of integral local
unit factors. These are the analytic algebra needed for the local R shapes;
no factor-count or leading-constant identity for R is assumed here. -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma powerSeries_mul_constant_error_bound (f g : PowerSeries ℤ_[p])
    (a b : ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n (f-PowerSeries.C a)‖ ≤ B)
    (hg : ∀ n, ‖PowerSeries.coeff n (g-PowerSeries.C b)‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n (f*g-PowerSeries.C (a*b))‖ ≤ B := by
  have he : f*g-PowerSeries.C (a*b) =
      g*(f-PowerSeries.C a)+PowerSeries.C a*(g-PowerSeries.C b) := by
    rw [map_mul]
    ring
  rw [he, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (restricted_mul_coeff_bound g _ B hB hf n)
      (restricted_mul_coeff_bound (PowerSeries.C a) _ B hB hg n))

theorem powerSeries_prod_constant_error_bound {ι : Type*} (s : Finset ι)
    (f : ι → PowerSeries ℤ_[p]) (a : ι → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ n, ‖PowerSeries.coeff n (f i-PowerSeries.C (a i))‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n ((∏ i ∈ s, f i)-PowerSeries.C (∏ i ∈ s, a i))‖ ≤ B := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => simpa using hB
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    apply powerSeries_mul_constant_error_bound _ _ _ _ B hB
    · exact hf i (Finset.mem_insert_self _ _)
    · intro k
      apply ih
      intro j hj
      exact hf j (Finset.mem_insert_of_mem hj)

theorem affineInverseSeries_constant_error_bound (a : ℤ_[p]ˣ) (b : ℤ_[p])
    (d n : ℕ) :
    ‖PowerSeries.coeff n (affineInverseSeries a b d-PowerSeries.C ((↑a⁻¹:ℤ_[p])^d))‖ ≤ ‖b‖ := by
  have he : affineInverseSeries a b d-PowerSeries.C ((↑a⁻¹:ℤ_[p])^d) =
      PowerSeries.C ((↑a⁻¹:ℤ_[p])^d)*(inverseOneSubSeries (-b*(↑a⁻¹:ℤ_[p])) d-1) := by
    unfold affineInverseSeries
    ring
  rw [he]
  apply restricted_mul_coeff_bound _ _ _ (norm_nonneg b)
  intro k
  exact (inverseOneSubSeries_error_bound _ d k).trans
    (by simpa only [norm_neg] using integral_coeff_mul_norm_le (-b) (↑a⁻¹:ℤ_[p]))

end
end Li2

end
