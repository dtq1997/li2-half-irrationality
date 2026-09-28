module
public import Li2Unified.Modular.Base.PositiveNormalization
public import Li2Unified.Modular.Base.DecayNormalization
public import Li2Unified.Modular.Base.PrimitiveReduction

set_option backward.privateInPublic true

@[expose] public section

/-! Same positive primitive polynomial, explicit zero branch. -/
open Polynomial
namespace Li2
noncomputable section

def dtilde (n : ℕ) : ℚ := d n / (Sn n ^ (2*n) / Fn n)

lemma dtilde_pos (n : ℕ) : 0 < dtilde n :=
  div_pos (d_pos n) (Qtilde_scale_pos n)

lemma dtilde_ne_zero (n : ℕ) : dtilde n ≠ 0 := (dtilde_pos n).ne'

theorem P_eq_dtilde_Qtilde (n : ℕ) :
    (P n).map (algebraMap ℤ ℚ) = C (dtilde n) * Qtilde n := by
  calc
    (P n).map (algebraMap ℤ ℚ) = C (d n) * Q n := P_eq_d_Q n
    _ = C (dtilde n) * Qtilde n := by
      rw [Qtilde, ← mul_assoc, ← C_mul, dtilde,
        div_mul_cancel₀ _ (Qtilde_scale_pos n).ne']

lemma P_isPrimitive_of_Qtilde_ne_zero (n : ℕ) (hn : Qtilde n ≠ 0) :
    (P n).IsPrimitive :=
  P_isPrimitive n ((Qtilde_ne_zero_iff n).mp hn)

theorem P_aeval_eq_dtilde_Qtilde (n : ℕ) (x : ℝ) :
    aeval x (P n) = (dtilde n : ℝ) * aeval x (Qtilde n) := by
  have h := congrArg (fun F : ℚ[X] => F.eval₂ (algebraMap ℚ ℝ) x)
    (P_eq_dtilde_Qtilde n)
  rw [eval₂_map, eval₂_mul, eval₂_C] at h
  simpa only [aeval_def, ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ] using! h

lemma abs_P_aeval_eq_dtilde_Qtilde (n : ℕ) (x : ℝ) :
    |aeval x (P n)| = (dtilde n : ℝ) * |aeval x (Qtilde n)| := by
  rw [P_aeval_eq_dtilde_Qtilde, abs_mul,
    abs_of_pos (show (0:ℝ) < (dtilde n : ℝ) by exact_mod_cast dtilde_pos n)]

end
end Li2

end
