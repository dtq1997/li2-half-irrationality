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

lemma P_coeff_eq_dtilde (n k : ℕ) :
    ((P n).coeff k : ℚ) = dtilde n * (Qtilde n).coeff k := by
  have h := congrArg (fun F : ℚ[X] => F.coeff k) (P_eq_dtilde_Qtilde n)
  simpa only [coeff_map, coeff_C_mul] using! h

lemma P_eq_zero_of_Q_eq_zero (n : ℕ) (hn : Q n = 0) : P n = 0 := by
  simp [P, primitiveQ, hn]

lemma P_eq_zero_iff_Q_eq_zero (n : ℕ) : P n = 0 ↔ Q n = 0 := by
  constructor
  · intro hP
    have h := P_eq_d_Q n
    rw [hP, Polynomial.map_zero] at h
    have hd : (C (d n) : ℚ[X]) ≠ 0 := by
      exact Polynomial.C_ne_zero.mpr (d_pos n).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hd
  · exact P_eq_zero_of_Q_eq_zero n

lemma Qtilde_eq_zero_iff_Q_eq_zero (n : ℕ) : Qtilde n = 0 ↔ Q n = 0 := by
  rw [Qtilde, mul_eq_zero, C_eq_zero]
  simp [(Qtilde_scale_pos n).ne']

lemma P_eq_zero_iff_Qtilde_eq_zero (n : ℕ) : P n = 0 ↔ Qtilde n = 0 :=
  (P_eq_zero_iff_Q_eq_zero n).trans (Qtilde_eq_zero_iff_Q_eq_zero n).symm

lemma P_isPrimitive_of_Qtilde_ne_zero (n : ℕ) (hn : Qtilde n ≠ 0) :
    (P n).IsPrimitive :=
  P_isPrimitive n ((Qtilde_ne_zero_iff n).mp hn)

theorem primitiveBinomial_zero_branch (n : ℕ) (hn : Q n = 0) :
    Qtilde n = 0 ∧ P n = 0 :=
  ⟨(Qtilde_eq_zero_iff_Q_eq_zero n).mpr hn, P_eq_zero_of_Q_eq_zero n hn⟩

lemma P_aeval_zero_of_Q_eq_zero (n : ℕ) (hn : Q n = 0) (x : ℝ) :
    aeval x (P n) = 0 := by
  rw [P_eq_zero_of_Q_eq_zero n hn, map_zero]

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
