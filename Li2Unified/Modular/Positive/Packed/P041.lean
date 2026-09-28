module
public import Li2Unified.Modular.Positive.Packed.P037
public import Li2Unified.Modular.Base.PrimeOuterTableIdentity
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.DecayBinomial
public import Li2Unified.Modular.Base.ParameterShift

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily
open Li2Unified.Stage0.HermitePreparation
open Li2.PrimeSums Finset Filter Topology Polynomial
open scoped BigOperators

/-- Transfer any actual Gauss bound to the primitive scale. -/
theorem parameter_dtilde_GV_lower (lam : ℚ) (n p : ℕ)
    [Fact p.Prime] (hne : Qtilde lam n ≠ 0) {r : ℚ}
    (hQ : Li2.GV p (Qtilde lam n) r) :
    r ≤ (-padicValRat p (dtilde lam n) : ℚ) := by
  obtain ⟨k, hk, hval, _⟩ := Qtilde_coeff_valuation_minimum lam p hne
  rcases hQ k with hz | hv
  · exact (hk hz).elim
  · rw [hval] at hv
    exact hv

/-- The existing five outer PNT windows bound the actual primitive content
provided their sharp *actual* Gauss estimates are supplied. -/
theorem parameter_outerWindowSum_le_valuation (lam : ℚ) (n : ℕ)
    (hne : Qtilde lam n ≠ 0)
    (houter : ∀ p ∈ Finset.Ioc n (4*n), ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      Li2.GV p (Qtilde lam n) (Li2.outerPrimeBound p n)) :
    outerWindowSum (n:ℝ) ≤
      ∑ p ∈ Finset.Ioc n (4*n),
        if p.Prime then
          ((-padicValRat p (dtilde lam n) : ℤ) : ℝ)*Real.log (p:ℝ)
        else 0 := by
  rw [outerWindowSum_eq_table]
  apply Finset.sum_le_sum
  intro p hpI
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    have hv : (Li2.outerPrimeBound p n : ℝ) ≤
        ((-padicValRat p (dtilde lam n) : ℤ) : ℝ) := by
      exact_mod_cast parameter_dtilde_GV_lower lam n p hne (houter p hpI hp)
    have hl : 0 ≤ Real.log (p:ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    simpa [cPrime, hp] using! mul_le_mul_of_nonneg_right hv hl
  · simp [cPrime, hp]

theorem outerWindowSum_eventually_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((7/2:ℝ)-ε)*(n:ℝ)^2 ≤ outerWindowSum (n:ℝ) := by
  have hmass : ∀ᶠ n : ℕ in atTop,
      (7/2:ℝ)-ε ≤ outerWindowSum (n:ℝ)/(n:ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith)
      outerWindowSum_nat_tendsto
  filter_upwards [hmass, eventually_ge_atTop (1:ℕ)] with n hmassn hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  exact (le_div_iff₀ (sq_pos_of_pos hnpos)).mp hmassn

theorem parameter_outer_eventually_conditional (lam : ℚ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Qtilde lam n ≠ 0 →
      (∀ p ∈ Finset.Ioc n (4*n), ∀ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        Li2.GV p (Qtilde lam n) (Li2.outerPrimeBound p n)) →
      ((7/2:ℝ)-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ Finset.Ioc n (4*n),
          if p.Prime then
            ((-padicValRat p (dtilde lam n) : ℤ) : ℝ)*Real.log (p:ℝ)
          else 0 := by
  filter_upwards [outerWindowSum_eventually_lower ε hε] with n hlimit
  intro hne houter
  exact hlimit.trans (parameter_outerWindowSum_le_valuation lam n hne houter)

/-- Exact strength check: the general normalized Gram floor is strictly
weaker than the required sharp outer floor at an actual prime. -/
theorem normalized_outer_gap_30_43 :
    (43:ℕ).Prime ∧ 30 < 43 ∧ 43 ≤ 4*30 ∧
      normalizedDetLower 30 43 = (-2:ℚ) ∧
      Li2.outerPrimeBound 43 30 = (6:ℚ) := by
  refine ⟨by decide, by omega, by omega, ?_, ?_⟩
  · norm_num [normalizedDetLower]
  · norm_num [Li2.outerPrimeBound]

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_outerWindowSum_le_valuation
#print axioms Li2Unified.Proofs.Arithmetic.parameter_outer_eventually_conditional
#print axioms Li2Unified.Proofs.Arithmetic.normalized_outer_gap_30_43

end

section
open Polynomial
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- The original parameter functional on the Newton basis. -/
def binomMoment (lam : ℚ) (k : ℕ) : ℚ := Li2.parameterG lam (Li2.binomPoly k)

lemma binomMoment_zero (lam : ℚ) : binomMoment lam 0 = lam / (1-lam) := by
  rw [binomMoment, Li2.binomPoly_zero, ← C_1, ← monomial_zero_left,
    Li2.parameterG_monomial]
  simp [Li2.parameterMoment]

lemma binomMoment_succ (lam : ℚ) (h1 : lam ≠ 1) (k : ℕ) :
    (1-lam) * binomMoment lam (k+1) =
      lam * (binomMoment lam k + (Li2.binomPoly (k+1)).eval 1) := by
  have h := Li2.parameterG_shift_one lam h1 (Li2.binomPoly (k+1))
  rw [Li2.binomPoly_succ_comp_add_one, Li2.parameterG_add] at h
  simp only [binomMoment] at h ⊢
  linear_combination -h

/-- Newton expansion of the same `parameterG` used by `numeratorFunctional`. -/
theorem parameterG_newton (lam : ℚ) {g : ℚ[X]} {d : ℕ}
    (hg : g.natDegree ≤ d) :
    Li2.parameterG lam g =
      ∑ k ∈ Finset.range (d+1), Li2.newtonCoeff g 0 k * binomMoment lam k := by
  conv_lhs => rw [Li2.newton_expansion hg 0]
  simp only [map_zero, sub_zero, comp_X]
  rw [Li2.parameterG_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Li2.parameterG_C_mul]
  rfl

/-- At a prime where `lam/(1-lam)` is integral, every Newton moment is integral. -/
theorem binomMoment_VG (p : ℕ) [Fact p.Prime] (lam : ℚ) (h1 : lam ≠ 1)
    (hratio : Li2.VG p (lam/(1-lam)) 0) (k : ℕ) :
    Li2.VG p (binomMoment lam k) 0 := by
  induction k with
  | zero => simpa only [binomMoment_zero] using! hratio
  | succ k ih =>
    have hden : 1-lam ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have he : binomMoment lam (k+1) =
        lam/(1-lam) * (binomMoment lam k + (Li2.binomPoly (k+1)).eval 1) := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hden).mpr
      have hs := binomMoment_succ lam h1 k
      nlinarith
    rw [he]
    simpa only [add_zero] using!
      hratio.mul (ih.add (Li2.binomPoly_eval_int_VG p (k+1) 1))

/-- Integer values in a finite window bound `parameterG` at every good prime. -/
theorem parameterG_VG_of_integral_ratio (p : ℕ) [Fact p.Prime]
    (lam : ℚ) (h1 : lam ≠ 1) (hratio : Li2.VG p (lam/(1-lam)) 0)
    {g : ℚ[X]} {d : ℕ} (hg : g.natDegree ≤ d) (r : ℚ)
    (hv : ∀ i ≤ d, Li2.VG p (g.eval (i:ℚ)) r) :
    Li2.VG p (Li2.parameterG lam g) r := by
  rw [parameterG_newton lam hg]
  apply Li2.VG.sum
  intro k hk
  have hk' : k ≤ d := by simp at hk; omega
  have hc := Li2.newtonCoeff_VG p 0 r k
    (fun i hi => by simpa using! hv i (hi.trans hk'))
  simpa using! hc.mul (binomMoment_VG p lam h1 hratio k)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameterG_newton
#print axioms Li2Unified.Proofs.Arithmetic.parameterG_VG_of_integral_ratio

end


end
