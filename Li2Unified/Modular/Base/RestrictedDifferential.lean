module
public import Li2Unified.Modular.Base.RestrictedFunctional
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

/-! The two bounded differential functionals U(f)=G((Xf)') and V(f)=G(f'). -/
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def derivativeMoments (μ : ℕ → ℤ_[p]) : ℕ → ℤ_[p]
  | 0 => 0
  | n+1 => (n+1:ℕ)*μ n

def restrictedU (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) : ℤ_[p] :=
  restrictedMoment (fun n => (n+1:ℕ)*μ n) f

def restrictedV (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) : ℤ_[p] :=
  restrictedMoment (derivativeMoments μ) f

theorem restrictedU_summable (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f*((n+1:ℕ)*μ n)) :=
  restrictedMoment_summable _ _ hf

theorem restrictedV_summable (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    Summable (fun n => PowerSeries.coeff n f*derivativeMoments μ n) :=
  restrictedMoment_summable _ _ hf

theorem restrictedU_derivative (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) :
    restrictedU μ f = restrictedMoment μ
      (PowerSeries.derivative (ℤ_[p]) (PowerSeries.X*f)) := by
  unfold restrictedU restrictedMoment
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul]
  push_cast
  ring

theorem restrictedV_derivative (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p])
    (hf : PowerSeries.IsRestricted 1 f) :
    restrictedV μ f = restrictedMoment μ (PowerSeries.derivative (ℤ_[p]) f) := by
  have he := (restrictedV_summable μ f hf).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, derivativeMoments, mul_zero, zero_add] at he
  unfold restrictedV restrictedMoment derivativeMoments
  rw [← he]
  apply tsum_congr
  intro n
  rw [PowerSeries.coeff_derivative]
  push_cast
  ring

theorem restrictedU_norm_le (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) (B : ℝ)
    (hB : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) : ‖restrictedU μ f‖ ≤ B :=
  restrictedMoment_norm_le _ _ _ hB

theorem restrictedV_norm_le (μ : ℕ → ℤ_[p]) (f : PowerSeries ℤ_[p]) (B : ℝ)
    (hB : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) : ‖restrictedV μ f‖ ≤ B :=
  restrictedMoment_norm_le _ _ _ hB

end
end Li2

end
