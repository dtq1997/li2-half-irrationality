module
public import Li2Unified.Modular.Positive.Packed.P048
public import Li2Unified.Modular.Positive.Packed.P036
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Base.RationalPrimeLog

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Polynomial
open scoped BigOperators

/-- The actual parameter-family Gram entry is integral at every prime above
its entire pole range. -/
theorem parameter_binomGram_entry_GV_large (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : Li2.VG p (lam/(1-lam)) 0)
    (hlam : Li2.VG p lam 0) (hinv : Li2.VG p lam⁻¹ 0)
    {n : ℕ} (hn : 1 ≤ n) (hpn : 4*n < p)
    {a b : ℕ} (ha : a < 2*n) (hb : b < 2*n) :
    Li2.GV p (Li2Unified.ParameterFamily.numeratorFunctional lam (4*n)
      (Li2.gramNum n a b)) 0 := by
  have hlogK : Nat.log p (4*n) = 0 :=
    Nat.log_eq_zero_iff.mpr (Or.inl hpn)
  have hE : 3*n+a+b-4*n < p := by omega
  have hlogE : Nat.log p (3*n+a+b-4*n) = 0 :=
    Nat.log_eq_zero_iff.mpr (Or.inl hE)
  unfold Li2Unified.ParameterFamily.numeratorFunctional
  apply Li2.GV.add
  · apply Li2.GV.C
    set q := Li2.gramNum n a b /ₘ Li2.D (4*n)
    have hq : Li2.GV p q 0 := parameter_gramQuot_GV_large p n a b hpn ha hb
    have hdeg : q.natDegree ≤ 3*n+a+b-4*n := Li2.gramQuot_natDegree_le n a b
    have hu := parameterU_VG_of_integer_values p lam h1 hratio hdeg 0
      (fun i => by
        simpa using! (Li2.VG.eval hq (Li2.VG.intCast i)))
    simpa [hlogE] using! hu
  · apply Li2.GV.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : Li2.VG p ((Li2.gramNum n a b).eval (-(j:ℚ)) /
        ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))) 0 :=
      Li2.gramRes_VG p n a b hj1 hj2
    have hc : Li2.VG p ((j:ℚ)*lam⁻¹^j) 0 := by
      simpa using! (Li2.VG.natCast (p := p) j).mul (hinv.pow j)
    have ht : Li2.VG p (Li2.parameterTau lam j) 0 := by
      simpa [hlogK] using! parameterTau_VG_log p lam hlam hj2
    have hlin : Li2.GV p (X - C (Li2.parameterTau lam j)) 0 :=
      Li2.GV.X.sub (Li2.GV.C ht)
    simpa using! (Li2.GV.C hres).mul ((Li2.GV.C hc).mul hlin)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_binomGram_entry_GV_large

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Polynomial
open scoped BigOperators

/-- Actual parameter-family determinant is integral outside the pole range. -/
theorem parameter_Qtilde_GV_large (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : Li2.VG p (lam/(1-lam)) 0)
    (hlam : Li2.VG p lam 0) (hinv : Li2.VG p lam⁻¹ 0)
    {n : ℕ} (hn : 1 ≤ n) (hpn : 4*n < p) :
    Li2.GV p (Qtilde lam n) 0 := by
  rw [Qtilde_eq_binomGram_det]
  have hdet := Li2.det_GV (p := p) (binomGram lam n)
    (fun _ => (0:ℚ)) (fun _ => (0:ℚ)) (fun a b => by
      change Li2.GV p (numeratorFunctional lam (4*n)
        (Li2.gramNum n a b)) (0+0)
      simpa using! parameter_binomGram_entry_GV_large p lam h1 hratio hlam hinv
        hn hpn a.isLt b.isLt)
  simpa using! hdet

/-- Primitive scale has no negative denominator contribution above all poles. -/
theorem parameter_dtilde_large_val_nonneg (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : Li2.VG p (lam/(1-lam)) 0)
    (hlam : Li2.VG p lam 0) (hinv : Li2.VG p lam⁻¹ 0)
    {n : ℕ} (hn : 1 ≤ n) (hpn : 4*n < p)
    (hne : Qtilde lam n ≠ 0) :
    0 ≤ -padicValRat p (dtilde lam n) := by
  obtain ⟨k, hk, hval, _⟩ := Qtilde_coeff_valuation_minimum lam p hne
  have hv := (parameter_Qtilde_GV_large p lam h1 hratio hlam hinv hn hpn) k
  rcases hv with hz | hv
  · exact (hk hz).elim
  · rw [hval] at hv
    exact_mod_cast hv

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_Qtilde_GV_large
#print axioms Li2Unified.Proofs.Arithmetic.parameter_dtilde_large_val_nonneg

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf

/-- Literal positive-half content contribution beyond the last pole. -/
theorem posHalf_large_content_raw (n p : ℕ) (hn : 1 ≤ n)
    (hp : p.Prime) (hpn : 4*n < p)
    (hne : Instances.PosHalf.Qtilde n ≠ 0) :
    0 ≤ ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hp1 : ¬ p ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    omega
  have hu := inverseParameter_unit (p := p) 2 (by norm_num) hp2
  have hlam : Li2.VG p lambda 0 := by
    rw [lambda_eq_inverse]
    right
    rw [hu.2]
    norm_num
  have hinv : Li2.VG p lambda⁻¹ 0 := by
    rw [lambda_eq_inverse]
    exact Li2.rational_unit_inverse_VG (inverseParameter 2) hu.1 hu.2
  have hratio : Li2.VG p (lambda/(1-lambda)) 0 := by
    rw [lambda_eq_inverse]
    exact inverseParameter_moment_integral 2 (by norm_num) hp2 hp1
  have hv : 0 ≤ ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ) := by
    exact_mod_cast parameter_dtilde_large_val_nonneg p lambda lambda_ne_one
      hratio hlam hinv hn hpn hne
  have hlog : 0 ≤ Real.log (p:ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact mul_nonneg hv hlog

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_large_content_raw

end


end
