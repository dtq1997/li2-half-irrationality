module
public import Li2Unified.Modular.Positive.Packed.P035
public import Li2Unified.Modular.Base.PrimitiveCoefficientMinimum

set_option backward.privateInPublic true

@[expose] public section

section
/-! Positive primitive normalization of the same parameter determinant.
The zero branch is total, and no primitive assertion is made at zero. -/
open Polynomial
namespace Li2Unified.ParameterFamily
noncomputable section

def primitiveQ (lam : ℚ) (n : ℕ) : ℤ[X] :=
  if Q lam n = 0 then 0 else
    (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q lam n)).primPart

theorem primitiveQ_isPrimitive (lam : ℚ) (n : ℕ) (hn : Q lam n ≠ 0) :
    (primitiveQ lam n).IsPrimitive := by
  simp only [primitiveQ, if_neg hn]
  exact Polynomial.isPrimitive_primPart _

theorem primitiveQ_natDegree_le (lam : ℚ) (n : ℕ) : (primitiveQ lam n).natDegree ≤ 2*n := by
  unfold primitiveQ
  split_ifs with hn
  · simp
  rw [Polynomial.natDegree_primPart]
  apply le_trans _ (Q_natDegree_le lam n)
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply Polynomial.notMem_support_iff.mp
  intro h
  have hs := IsLocalization.integerNormalization_support (nonZeroDivisors ℤ) (Q lam n)
  exact (Polynomial.notMem_support_iff.mpr (Polynomial.coeff_eq_zero_of_natDegree_lt hk)) (hs h)

theorem primitiveQ_proportional (lam : ℚ) (n : ℕ) :
    ∃ a : ℚ, a ≠ 0 ∧ (primitiveQ lam n).map (algebraMap ℤ ℚ) = C a * Q lam n := by
  by_cases hn : Q lam n = 0
  · exact ⟨1, one_ne_zero, by simp [primitiveQ, hn]⟩
  let R := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q lam n)
  have hR : R ≠ 0 := fun hz => hn (IsFractionRing.integerNormalization_eq_zero_iff.mp hz)
  have hcont : R.content ≠ 0 := fun hz => hR (Polynomial.content_eq_zero_iff.mp hz)
  have hcontQ : (R.content : ℚ) ≠ 0 := by exact_mod_cast hcont
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Q lam n)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  refine ⟨(b : ℚ)/(R.content : ℚ), div_ne_zero hbQ hcontQ, ?_⟩
  apply Polynomial.ext
  intro k
  have hfac := congrArg (fun f : ℤ[X] => (f.map (algebraMap ℤ ℚ)).coeff k)
    R.eq_C_content_mul_primPart
  have hco : (b : ℚ) * (Q lam n).coeff k = (R.content : ℚ) * (R.primPart.coeff k : ℚ) := by
    rw [show R.map (algebraMap ℤ ℚ) = b • Q lam n from hmap] at hfac
    simpa using! hfac
  simp only [primitiveQ, if_neg hn, coeff_map, coeff_C_mul]
  change (R.primPart.coeff k : ℚ) = (b : ℚ)/(R.content : ℚ) * (Q lam n).coeff k
  apply (mul_left_cancel₀ hcontQ)
  field_simp
  nlinarith [hco]


def primitiveScale (lam : ℚ) (n : ℕ) : ℚ := (primitiveQ_proportional lam n).choose

lemma primitiveScale_ne_zero (lam : ℚ) (n : ℕ) : primitiveScale lam n ≠ 0 :=
  (primitiveQ_proportional lam n).choose_spec.1

lemma primitiveScale_spec (lam : ℚ) (n : ℕ) :
    (primitiveQ lam n).map (algebraMap ℤ ℚ) = C (primitiveScale lam n) * Q lam n :=
  (primitiveQ_proportional lam n).choose_spec.2

def P (lam : ℚ) (n : ℕ) : ℤ[X] :=
  if 0 < primitiveScale lam n then primitiveQ lam n else -primitiveQ lam n

def d (lam : ℚ) (n : ℕ) : ℚ := |primitiveScale lam n|

theorem d_pos (lam : ℚ) (n : ℕ) : 0 < d lam n := abs_pos.mpr (primitiveScale_ne_zero lam n)

theorem P_eq_d_Q (lam : ℚ) (n : ℕ) : (P lam n).map (algebraMap ℤ ℚ) = C (d lam n) * Q lam n := by
  by_cases h : 0 < primitiveScale lam n
  · simpa only [P, if_pos h, d, abs_of_pos h] using! primitiveScale_spec lam n
  · have hneg : primitiveScale lam n < 0 :=
      lt_of_le_of_ne (le_of_not_gt h) (primitiveScale_ne_zero lam n)
    simp only [P, if_neg h, Polynomial.map_neg, primitiveScale_spec,
      d, abs_of_neg hneg, map_neg, neg_mul]

theorem P_natDegree_le (lam : ℚ) (n : ℕ) : (P lam n).natDegree ≤ 2*n := by
  unfold P
  split_ifs <;> simpa using! primitiveQ_natDegree_le lam n

theorem P_isPrimitive (lam : ℚ) (n : ℕ) (hn : Q lam n ≠ 0) : (P lam n).IsPrimitive := by
  unfold P
  split_ifs
  · exact primitiveQ_isPrimitive lam n hn
  · apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
    intro r hr
    apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp (primitiveQ_isPrimitive lam n hn) r
    simpa using! hr


def dtilde (lam : ℚ) (n : ℕ) : ℚ := d lam n / (Li2.Sn n ^ (2*n) / Li2.Fn n)

lemma dtilde_pos (lam : ℚ) (n : ℕ) : 0 < dtilde lam n :=
  div_pos (d_pos lam n) (Li2.Qtilde_scale_pos n)

lemma dtilde_ne_zero (lam : ℚ) (n : ℕ) : dtilde lam n ≠ 0 := (dtilde_pos lam n).ne'

theorem P_eq_dtilde_Qtilde (lam : ℚ) (n : ℕ) :
    (P lam n).map (algebraMap ℤ ℚ) = C (dtilde lam n) * Qtilde lam n := by
  calc
    (P lam n).map (algebraMap ℤ ℚ) = C (d lam n) * Q lam n := P_eq_d_Q lam n
    _ = C (dtilde lam n) * Qtilde lam n := by
      rw [Qtilde, ← mul_assoc, ← C_mul, dtilde,
        div_mul_cancel₀ _ (Li2.Qtilde_scale_pos n).ne']

lemma P_coeff_eq_dtilde (lam : ℚ) (n k : ℕ) :
    ((P lam n).coeff k : ℚ) = dtilde lam n * (Qtilde lam n).coeff k := by
  have h := congrArg (fun F : ℚ[X] => F.coeff k) (P_eq_dtilde_Qtilde lam n)
  simpa only [coeff_map, coeff_C_mul] using! h

lemma P_eq_zero_of_Q_eq_zero (lam : ℚ) (n : ℕ) (hn : Q lam n = 0) : P lam n = 0 := by
  simp [P, primitiveQ, hn]

lemma P_eq_zero_iff_Q_eq_zero (lam : ℚ) (n : ℕ) : P lam n = 0 ↔ Q lam n = 0 := by
  constructor
  · intro hP
    have h := P_eq_d_Q lam n
    rw [hP, Polynomial.map_zero] at h
    have hd : (C (d lam n) : ℚ[X]) ≠ 0 := by
      exact Polynomial.C_ne_zero.mpr (d_pos lam n).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hd
  · exact P_eq_zero_of_Q_eq_zero lam n

lemma Qtilde_eq_zero_iff_Q_eq_zero (lam : ℚ) (n : ℕ) : Qtilde lam n = 0 ↔ Q lam n = 0 := by
  rw [Qtilde, mul_eq_zero, C_eq_zero]
  simp [(Li2.Qtilde_scale_pos n).ne']

lemma P_eq_zero_iff_Qtilde_eq_zero (lam : ℚ) (n : ℕ) : P lam n = 0 ↔ Qtilde lam n = 0 :=
  (P_eq_zero_iff_Q_eq_zero lam n).trans (Qtilde_eq_zero_iff_Q_eq_zero lam n).symm

lemma P_isPrimitive_of_Qtilde_ne_zero (lam : ℚ) (n : ℕ) (hn : Qtilde lam n ≠ 0) :
    (P lam n).IsPrimitive :=
  P_isPrimitive lam n ((Qtilde_ne_zero_iff lam n).mp hn)

theorem primitiveBinomial_zero_branch (lam : ℚ) (n : ℕ) (hn : Q lam n = 0) :
    Qtilde lam n = 0 ∧ P lam n = 0 :=
  ⟨(Qtilde_eq_zero_iff_Q_eq_zero lam n).mpr hn, P_eq_zero_of_Q_eq_zero lam n hn⟩

lemma P_aeval_zero_of_Q_eq_zero (lam : ℚ) (n : ℕ) (hn : Q lam n = 0) (x : ℝ) :
    aeval x (P lam n) = 0 := by
  rw [P_eq_zero_of_Q_eq_zero lam n hn, map_zero]

theorem P_aeval_eq_dtilde_Qtilde (lam : ℚ) (n : ℕ) (x : ℝ) :
    aeval x (P lam n) = (dtilde lam n : ℝ) * aeval x (Qtilde lam n) := by
  have h := congrArg (fun F : ℚ[X] => F.eval₂ (algebraMap ℚ ℝ) x)
    (P_eq_dtilde_Qtilde lam n)
  rw [eval₂_map, eval₂_mul, eval₂_C] at h
  simpa only [aeval_def, ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ] using! h

lemma abs_P_aeval_eq_dtilde_Qtilde (lam : ℚ) (n : ℕ) (x : ℝ) :
    |aeval x (P lam n)| = (dtilde lam n : ℝ) * |aeval x (Qtilde lam n)| := by
  rw [P_aeval_eq_dtilde_Qtilde, abs_mul,
    abs_of_pos (show (0:ℝ) < (dtilde lam n : ℝ) by exact_mod_cast dtilde_pos lam n)]


 theorem primitiveQ_negHalf (n : ℕ) : primitiveQ (-1/2) n = Li2.primitiveQ n := by
  unfold primitiveQ Li2.primitiveQ
  rw [Q_negHalf]

 theorem primitiveScale_negHalf (n : ℕ) : primitiveScale (-1/2) n = Li2.primitiveScale n := by
  unfold primitiveScale Li2.primitiveScale
  congr 1 <;> simp only [primitiveQ_negHalf, Q_negHalf]

 theorem P_negHalf (n : ℕ) : P (-1/2) n = Li2.P n := by
  simp only [P, Li2.P, primitiveScale_negHalf, primitiveQ_negHalf]

 theorem d_negHalf (n : ℕ) : d (-1/2) n = Li2.d n := by
  simp only [d, Li2.d, primitiveScale_negHalf]

 theorem dtilde_negHalf (n : ℕ) : dtilde (-1/2) n = Li2.dtilde n := by
  simp only [dtilde, Li2.dtilde, d_negHalf]

 theorem Qtilde_coeff_valuation_minimum (lam : ℚ) (p : ℕ) [Fact p.Prime] {n : ℕ}
    (hn : Qtilde lam n ≠ 0) :
    ∃ k, (Qtilde lam n).coeff k ≠ 0 ∧
      padicValRat p ((Qtilde lam n).coeff k) = -padicValRat p (dtilde lam n) ∧
      ∀ j, (Qtilde lam n).coeff j ≠ 0 →
        padicValRat p ((Qtilde lam n).coeff k) ≤ padicValRat p ((Qtilde lam n).coeff j) :=
  Li2.primitive_scale_coeff_valuation_minimum p (P lam n)
    (P_isPrimitive_of_Qtilde_ne_zero lam n hn) (Qtilde lam n) (dtilde lam n)
    (dtilde_ne_zero lam n) (P_eq_dtilde_Qtilde lam n)

end
end Li2Unified.ParameterFamily

end


end
