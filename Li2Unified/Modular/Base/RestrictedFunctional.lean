module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.PowerSeries.Restricted
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.RingTheory.PowerSeries.Derivative

set_option backward.privateInPublic true

@[expose] public section

/-! A bounded moment functional on restricted integral power series.
Its convergence is proved separately from the totalized `tsum` definition. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def restrictedMoment (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) : ℤ_[p] :=
  ∑' n, PowerSeries.coeff n f * μ n

lemma restricted_coeff_tendsto {f : PowerSeries ℤ_[p]}
    (hf : PowerSeries.IsRestricted 1 f) :
    Tendsto (fun n => ‖PowerSeries.coeff n f‖) atTop (𝓝 0) := by
  simpa only [one_pow, mul_one] using (PowerSeries.isRestricted_iff' _ _).mp hf

lemma integral_coeff_mul_norm_le (a b : ℤ_[p]) : ‖a*b‖ ≤ ‖a‖ := by
  calc
    ‖a*b‖ ≤ ‖a‖*‖b‖ := norm_mul_le _ _
    _ ≤ ‖a‖*1 := mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ‖a‖ := mul_one _

theorem restrictedMoment_summable (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f * μ n) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => integral_coeff_mul_norm_le _ _)
    (restricted_coeff_tendsto hf)

theorem restrictedMoment_norm_le (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) (C : ℝ)
    (hC : ∀ n, ‖PowerSeries.coeff n f‖ ≤ C) : ‖restrictedMoment μ f‖ ≤ C := by
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro n
  exact (integral_coeff_mul_norm_le _ _).trans (hC n)

theorem restrictedMoment_add (μ : ℕ → ℤ_[p]) (f g : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    restrictedMoment μ (f+g) = restrictedMoment μ f + restrictedMoment μ g := by
  unfold restrictedMoment
  simp only [map_add, add_mul]
  exact Summable.tsum_add (restrictedMoment_summable μ f hf) (restrictedMoment_summable μ g hg)

theorem restrictedMoment_smul (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (a : ℤ_[p]) :
    restrictedMoment μ (a • f) = a * restrictedMoment μ f := by
  unfold restrictedMoment
  simp only [map_smul, smul_eq_mul, mul_assoc]
  exact Summable.tsum_mul_left a (restrictedMoment_summable μ f hf)

theorem polynomial_isRestricted (P : (ℤ_[p])[X]) :
    PowerSeries.IsRestricted 1 (P : PowerSeries ℤ_[p]) := by
  rw [PowerSeries.isRestricted_iff']
  simp only [one_pow, mul_one]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (P.natDegree+1)] with n hn
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

theorem restrictedMoment_polynomial (μ : ℕ → ℤ_[p]) (P : (ℤ_[p])[X]) :
    restrictedMoment μ (P : PowerSeries ℤ_[p]) = P.sum (fun n a => a*μ n) := by
  unfold restrictedMoment Polynomial.sum
  simp only [Polynomial.coeff_coe]
  apply tsum_eq_sum
  intro n hn
  rw [Polynomial.notMem_support_iff.mp hn, zero_mul]

end
end Li2

end
