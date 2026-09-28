module
public import Li2Unified.Modular.Base.RestrictedShift

set_option backward.privateInPublic true

@[expose] public section

/-! Integral divided differences on the closed p-adic disc. The quotient is
constructed by convergent coefficient sums, then identified by an exact identity. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def restrictedDivDiff (c : ℤ_[p]) (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n+k+1) f*c^k

theorem restrictedDivDiff_summable (c : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n+k+1) f*c^k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun k : ℕ => ‖PowerSeries.coeff (n+k+1) f‖) atTop (𝓝 0) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
      (restricted_coeff_tendsto hf).comp (tendsto_add_atTop_nat (n+1))
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun k => integral_coeff_mul_norm_le _ _) ht

theorem restrictedDivDiff_coeff_bound (c : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (n : ℕ) (B : ℝ) (hB : ∀ k, ‖PowerSeries.coeff (n+k+1) f‖ ≤ B) :
    ‖PowerSeries.coeff n (restrictedDivDiff c f)‖ ≤ B := by
  simp only [restrictedDivDiff, PowerSeries.coeff_mk]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  exact (integral_coeff_mul_norm_le _ _).trans (hB k)

theorem restrictedDivDiff_isRestricted (c : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) : PowerSeries.IsRestricted 1 (restrictedDivDiff c f) := by
  rw [PowerSeries.isRestricted_iff', Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (restricted_coeff_tendsto hf) (ε/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  simp only [one_pow, mul_one, Real.dist_eq, sub_zero, abs_norm] at hN ⊢
  apply lt_of_le_of_lt (restrictedDivDiff_coeff_bound c f n (ε/2) ?_) (by linarith)
  intro k
  exact (hN (n+k+1) (by omega)).le

theorem restrictedDivDiff_coeff_recurrence (c : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (n : ℕ) :
    PowerSeries.coeff n (restrictedDivDiff c f) = PowerSeries.coeff (n+1) f +
      c*PowerSeries.coeff (n+1) (restrictedDivDiff c f) := by
  have he := (restrictedDivDiff_summable c f hf n).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.add_zero, pow_zero, mul_one] at he
  simp only [restrictedDivDiff, PowerSeries.coeff_mk]
  rw [← he, ← (restrictedDivDiff_summable c f hf (n+1)).tsum_mul_left c]
  congr 1
  apply tsum_congr
  intro k
  have hi : n+(k+1)+1 = (n+1)+k+1 := by omega
  rw [hi, pow_succ]
  ring

theorem restrictedDivDiff_eval_identity (c : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    restrictedEval c f = PowerSeries.coeff 0 f + c*PowerSeries.coeff 0 (restrictedDivDiff c f) := by
  have he := (restrictedMoment_summable (fun n => c^n) f hf).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, pow_zero, mul_one] at he
  unfold restrictedEval restrictedMoment
  rw [← he]
  simp only [restrictedDivDiff, PowerSeries.coeff_mk, Nat.zero_add]
  have hmul := (restrictedDivDiff_summable c f hf 0).tsum_mul_left c
  simp only [Nat.zero_add] at hmul
  rw [← hmul]
  congr 1
  apply tsum_congr
  intro k
  simp only [Nat.zero_add, pow_succ]
  ring

theorem restrictedDivDiff_identity (c : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    (PowerSeries.X-PowerSeries.C c)*restrictedDivDiff c f =
      f-PowerSeries.C (restrictedEval c f) := by
  rw [sub_mul]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp only [map_sub, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_zero_C, zero_sub]
    rw [restrictedDivDiff_eval_identity c f hf]
    ring
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_C, sub_zero]
    rw [restrictedDivDiff_coeff_recurrence c f hf n]
    ring

end
end Li2

end
