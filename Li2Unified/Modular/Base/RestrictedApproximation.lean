module
public import Li2Unified.Modular.Base.RestrictedTranslation
public import Mathlib.RingTheory.PowerSeries.Trunc

set_option backward.privateInPublic true

@[expose] public section

/-! Polynomial truncations converge for the bounded moment functional, including
after any integral translation. The estimates are uniform in coefficient index. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem restrictedMoment_sub (μ : ℕ → ℤ_[p]) (f g : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    restrictedMoment μ (f-g) = restrictedMoment μ f-restrictedMoment μ g := by
  unfold restrictedMoment
  simp only [map_sub, sub_mul]
  exact Summable.tsum_sub (restrictedMoment_summable μ f hf) (restrictedMoment_summable μ g hg)

theorem restrictedTranslate_sub (a : ℤ_[p]) (f g : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    restrictedTranslate a (f-g) = restrictedTranslate a f-restrictedTranslate a g := by
  apply PowerSeries.ext
  intro n
  simp only [restrictedTranslate, PowerSeries.coeff_mk, map_sub, sub_mul]
  exact Summable.tsum_sub (restrictedTranslate_summable a f hf n)
    (restrictedTranslate_summable a g hg n)

lemma trunc_error_coeff_bound (f : PowerSeries ℤ_[p]) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ n, N ≤ n → ‖PowerSeries.coeff n f‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n (f-(PowerSeries.trunc N f : PowerSeries ℤ_[p]))‖ ≤ B := by
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hn : n < N
  · simpa only [if_pos hn, sub_self, norm_zero] using hB
  · simpa only [if_neg hn, sub_zero] using htail n (by omega)

theorem restrictedMoment_trunc_bound (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ n, N ≤ n → ‖PowerSeries.coeff n f‖ ≤ B) :
    ‖restrictedMoment μ f-restrictedMoment μ (PowerSeries.trunc N f : PowerSeries ℤ_[p])‖ ≤ B := by
  rw [← restrictedMoment_sub μ f _ hf (polynomial_isRestricted _)]
  exact restrictedMoment_norm_le μ _ B (trunc_error_coeff_bound f N B hB htail)

theorem translatedMoment_trunc_bound (μ : ℕ → ℤ_[p]) (a : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (htail : ∀ n, N ≤ n → ‖PowerSeries.coeff n f‖ ≤ B) :
    ‖restrictedMoment μ (restrictedTranslate a f)-
      restrictedMoment μ (restrictedTranslate a (PowerSeries.trunc N f : PowerSeries ℤ_[p]))‖ ≤ B := by
  rw [← restrictedMoment_sub μ _ _ (restrictedTranslate_isRestricted a f hf)
    (restrictedTranslate_isRestricted a _ (polynomial_isRestricted _)),
    ← restrictedTranslate_sub a f _ hf (polynomial_isRestricted _)]
  apply restrictedMoment_norm_le
  intro n
  apply restrictedTranslate_coeff_bound
  intro k
  exact trunc_error_coeff_bound f N B hB htail (n+k)

theorem tendsto_of_trunc_error_bound (F : PowerSeries ℤ_[p] → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f)
    (hbound : ∀ N B, 0 ≤ B → (∀ n, N ≤ n → ‖PowerSeries.coeff n f‖ ≤ B) →
      ‖F f-F (PowerSeries.trunc N f : PowerSeries ℤ_[p])‖ ≤ B) :
    Tendsto (fun N => F (PowerSeries.trunc N f : PowerSeries ℤ_[p])) atTop (𝓝 (F f)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := (PowerSeries.IsRestricted.isRestricted_iff 1).mp hf (ε/2) (by linarith)
  simp only [one_pow, mul_one, Real.norm_eq_abs, abs_norm] at hN
  refine ⟨N, fun M hM => ?_⟩
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt (hbound M (ε/2) (by linarith) ?_) (by linarith)
  intro n hn
  exact (hN n (hM.trans hn)).le

theorem restrictedMoment_trunc_tendsto (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Tendsto (fun N => restrictedMoment μ (PowerSeries.trunc N f : PowerSeries ℤ_[p]))
      atTop (𝓝 (restrictedMoment μ f)) :=
  tendsto_of_trunc_error_bound (restrictedMoment μ) f hf (restrictedMoment_trunc_bound μ f hf)

theorem translatedMoment_trunc_tendsto (μ : ℕ → ℤ_[p]) (a : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Tendsto (fun N => restrictedMoment μ
      (restrictedTranslate a (PowerSeries.trunc N f : PowerSeries ℤ_[p])))
      atTop (𝓝 (restrictedMoment μ (restrictedTranslate a f))) :=
  tendsto_of_trunc_error_bound (fun g => restrictedMoment μ (restrictedTranslate a g))
    f hf (translatedMoment_trunc_bound μ a f hf)

end
end Li2

end
