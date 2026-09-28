module
public import Li2Unified.Modular.Positive.Packed.P030
public import Li2Unified.Modular.Positive.Packed.P038

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation
open Filter Topology Finset
open scoped BigOperators

/-- The strict finite-cell correction yields an eventual quadratic lower
bound at every fixed reciprocal cutoff. -/
theorem profileWindowClosedSumN_eventually_lower (N : ℕ)
    (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((-523/840:ℝ)+(2/3:ℝ)/((N+1:ℕ):ℝ)^2-ε)*(n:ℝ)^2 ≤
        profileWindowClosedSumN N n := by
  have hc := profile_cell_sum_N_lower N hN
  have hmass : ∀ᶠ n : ℕ in atTop,
      (-523/840:ℝ)+(2/3:ℝ)/((N+1:ℕ):ℝ)^2-ε ≤
        profileWindowClosedSumN N n/(n:ℝ)^2 :=
    Filter.Tendsto.eventually_const_le (by linarith)
      (profileWindowClosedSumN_tendsto N)
  filter_upwards [hmass, eventually_ge_atTop (1:ℕ)] with n hmassn hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  exact (le_div_iff₀ (sq_pos_of_pos hnpos)).mp hmassn

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowClosedSumN_eventually_lower

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Stage0.HermitePreparation
open Filter

/-- Every finite reciprocal cutoff has the sharp profile lower bound on
its actual primitive content, conditional only on the actual Gram estimate. -/
theorem parameter_mediumN_eventually (lam : ℚ) (N : ℕ) (hN : 2 ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 0 < n → Qtilde lam n ≠ 0 →
      (∀ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n,
        ∀ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          Li2.GV p (binomGram lam n).det (normalizedDetLower n p)) →
      ((-523/840:ℝ)+(2/3:ℝ)/((N+1:ℕ):ℝ)^2-ε)*(n:ℝ)^2 ≤
        ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n,
          if p.Prime then
            ((-padicValRat p (dtilde lam n) : ℤ) : ℝ)*Real.log (p:ℝ)
          else 0 := by
  filter_upwards [profileWindowClosedSumN_eventually_lower N hN ε hε] with n hprofile
  intro hn hne hgram
  exact hprofile.trans
    (parameter_profileWindowClosedSumN_le_valuation lam N n
      (by omega : 1 ≤ N) hn hne hgram)

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameter_mediumN_eventually

end


end
