module
public import Li2Unified.Modular.Base.RestrictedFunctional
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

set_option backward.privateInPublic true

@[expose] public section

/-! Integral translation on restricted p-adic power series, defined by convergent
binomial coefficient sums. Formal power-series substitution is not used. -/
open Filter Polynomial
open scoped Topology BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def restrictedTranslate (a : ℤ_[p]) (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.mk fun n => ∑' k : ℕ,
    PowerSeries.coeff (n+k) f * (Nat.choose (n+k) n : ℤ_[p]) * a^k

lemma translate_term_norm_le (a : ℤ_[p]) (f : PowerSeries ℤ_[p]) (n k : ℕ) :
    ‖PowerSeries.coeff (n+k) f * (Nat.choose (n+k) n : ℤ_[p]) * a^k‖ ≤
      ‖PowerSeries.coeff (n+k) f‖ := by
  rw [mul_assoc]
  exact integral_coeff_mul_norm_le _ _

theorem restrictedTranslate_summable (a : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n+k) f * (Nat.choose (n+k) n : ℤ_[p]) * a^k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun k : ℕ => ‖PowerSeries.coeff (n+k) f‖) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using (restricted_coeff_tendsto hf).comp (tendsto_add_atTop_nat n)
  exact squeeze_zero (fun _ => norm_nonneg _) (translate_term_norm_le a f n) ht

theorem restrictedTranslate_coeff_bound (a : ℤ_[p]) (f : PowerSeries ℤ_[p]) (n : ℕ)
    (B : ℝ) (hB : ∀ k, ‖PowerSeries.coeff (n+k) f‖ ≤ B) :
    ‖PowerSeries.coeff n (restrictedTranslate a f)‖ ≤ B := by
  simp only [restrictedTranslate, PowerSeries.coeff_mk]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le
  intro k
  exact (translate_term_norm_le a f n k).trans (hB k)

theorem restrictedTranslate_isRestricted (a : ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) : PowerSeries.IsRestricted 1 (restrictedTranslate a f) := by
  rw [PowerSeries.IsRestricted.isRestricted_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (PowerSeries.IsRestricted.isRestricted_iff 1).mp hf (ε/2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  simp only [one_pow, mul_one, Real.norm_eq_abs, abs_norm] at hN ⊢
  apply lt_of_le_of_lt (restrictedTranslate_coeff_bound a f n (ε/2) ?_) (by linarith)
  intro k
  exact (hN (n+k) (by omega)).le

theorem restrictedTranslate_add (a : ℤ_[p]) (f g : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) (hg : PowerSeries.IsRestricted 1 g) :
    restrictedTranslate a (f+g) = restrictedTranslate a f + restrictedTranslate a g := by
  apply PowerSeries.ext
  intro n
  simp only [restrictedTranslate, PowerSeries.coeff_mk, map_add, add_mul]
  exact Summable.tsum_add (restrictedTranslate_summable a f hf n)
    (restrictedTranslate_summable a g hg n)

theorem restrictedTranslate_polynomial (a : ℤ_[p]) (P : (ℤ_[p])[X]) :
    restrictedTranslate a (P : PowerSeries ℤ_[p]) =
      (P.comp (X+C a) : PowerSeries ℤ_[p]) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.coe_add, restrictedTranslate_add a _ _ (polynomial_isRestricted P)
      (polynomial_isRestricted Q), add_comp, Polynomial.coe_add, hP, hQ]
  | monomial m c =>
    apply PowerSeries.ext
    intro n
    simp only [restrictedTranslate, PowerSeries.coeff_mk, Polynomial.coeff_coe,
      monomial_comp, coeff_C_mul, coeff_X_add_C_pow]
    by_cases hnm : n ≤ m
    · rw [tsum_eq_single (m-n)]
      · have he : n+(m-n) = m := by omega
        simp [he, Polynomial.coeff_monomial, mul_comm, mul_left_comm, mul_assoc]
      · intro k hk
        have he : n+k ≠ m := by omega
        simp [Polynomial.coeff_monomial, he, Ne.symm he]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
      have hz (k : ℕ) : (monomial m c : (ℤ_[p])[X]).coeff (n+k) = 0 := by
        have he : n+k ≠ m := by omega
        simp [Polynomial.coeff_monomial, he, Ne.symm he]
      simp only [hz, zero_mul, tsum_zero]

end
end Li2

end
