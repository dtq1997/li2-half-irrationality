module
public import Li2Unified.Modular.Base.RestrictedFunctional

set_option backward.privateInPublic true

@[expose] public section

/-! Extend the integral moment functional to restricted series over Q_p.
Convergence and scalar linearity are proved without an integrality assumption
on the coefficients. The integral extension is checked against its original sum. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def fieldRestrictedMoment (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p]) : ℚ_[p] :=
  ∑' n, PowerSeries.coeff n f * (μ n : ℚ_[p])

lemma field_restricted_coeff_tendsto {f : PowerSeries ℚ_[p]}
    (hf : PowerSeries.IsRestricted 1 f) :
    Tendsto (fun n => ‖PowerSeries.coeff n f‖) atTop (𝓝 0) := by
  simpa only [one_pow, mul_one] using (PowerSeries.isRestricted_iff' _ _).mp hf

lemma field_integral_mul_norm_le (a : ℚ_[p]) (b : ℤ_[p]) : ‖a*(b:ℚ_[p])‖ ≤ ‖a‖ := by
  calc
    ‖a*(b:ℚ_[p])‖ ≤ ‖a‖*‖(b:ℚ_[p])‖ := norm_mul_le _ _
    _ ≤ ‖a‖*1 := mul_le_mul_of_nonneg_left (PadicInt.norm_le_one b) (norm_nonneg _)
    _ = ‖a‖ := mul_one _

theorem fieldRestrictedMoment_summable (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f * (μ n : ℚ_[p])) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => field_integral_mul_norm_le _ _)
    (field_restricted_coeff_tendsto hf)

theorem fieldRestrictedMoment_add (μ : ℕ → ℤ_[p]) (f g : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    fieldRestrictedMoment μ (f+g) = fieldRestrictedMoment μ f + fieldRestrictedMoment μ g := by
  unfold fieldRestrictedMoment
  simp only [map_add, add_mul]
  exact Summable.tsum_add (fieldRestrictedMoment_summable μ f hf) (fieldRestrictedMoment_summable μ g hg)

theorem fieldRestrictedMoment_smul (μ : ℕ → ℤ_[p]) (f : PowerSeries ℚ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (a : ℚ_[p]) :
    fieldRestrictedMoment μ (a • f) = a * fieldRestrictedMoment μ f := by
  unfold fieldRestrictedMoment
  simp only [map_smul, smul_eq_mul, mul_assoc]
  exact Summable.tsum_mul_left a (fieldRestrictedMoment_summable μ f hf)

theorem fieldRestrictedMoment_integral (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    fieldRestrictedMoment μ (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) f) =
      (restrictedMoment μ f : ℚ_[p]) := by
  have h := (restrictedMoment_summable μ f hf).map_tsum
    PadicInt.Coe.ringHom PadicInt.isOpenEmbedding_coe.continuous
  simpa only [fieldRestrictedMoment, restrictedMoment, PowerSeries.coeff_map,
    map_mul] using! h.symm

theorem fieldRestrictedMoment_polynomial (μ : ℕ → ℤ_[p]) (P : (ℚ_[p])[X]) :
    fieldRestrictedMoment μ (P : PowerSeries ℚ_[p]) = P.sum (fun n a => a*(μ n:ℚ_[p])) := by
  unfold fieldRestrictedMoment Polynomial.sum
  simp only [Polynomial.coeff_coe]
  apply tsum_eq_sum
  intro n hn
  rw [Polynomial.notMem_support_iff.mp hn, zero_mul]

end
end Li2

end
