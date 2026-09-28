module
public import Li2Unified.Modular.Base.DecayTaylor
public import Li2Unified.Modular.Base.MomentArithmetic

set_option backward.privateInPublic true

@[expose] public section

/-! the backward shift of G = parameterG (-1/2),
  G(R) = -sum_{m<M} (-2)^m R(-m) + (-2)^M G(R(X-M)),
exact in ℚ for every M. It replaces the manuscript's 2-adically convergent
reflected series by a finite identity plus an explicit tail. Also: for p != 3
the binomial moments are p-integral, so G(R) is bounded by the values of R. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma Gm_back_one (R : ℚ[X]) : Gm R = -2 * Gm (R.comp (X - 1)) - R.eval 0 := by
  have h := Gm_shift (R.comp (X - 1))
  have hc : (R.comp (X - 1)).comp (X + 1) = R := by
    rw [comp_assoc, sub_comp, X_comp, one_comp, add_sub_cancel_right, comp_X]
  rw [hc] at h
  have he : (R.comp (X - 1)).eval 1 = R.eval 0 := by simp [eval_comp]
  rw [he] at h
  linarith

theorem Gm_back (R : ℚ[X]) (M : ℕ) :
    Gm R = -(∑ m ∈ Finset.range M, (-2:ℚ)^m * R.eval (-(m:ℚ))) +
      (-2:ℚ)^M * Gm (R.comp (X - C (M:ℚ))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, Gm_back_one (R.comp (X - C (M:ℚ)))]
    have hc : (R.comp (X - C (M:ℚ))).comp (X - 1) = R.comp (X - C ((M+1 : ℕ):ℚ)) := by
      rw [comp_assoc, sub_comp, X_comp, C_comp]
      congr 1
      push_cast
      rw [map_add, map_one]
      ring
    have he : (R.comp (X - C (M:ℚ))).eval 0 = R.eval (-(M:ℚ)) := by
      simp [eval_comp]
    rw [hc, he, Finset.sum_range_succ, pow_succ]
    ring

lemma binomMoment_VG_of_ne_three (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) (k : ℕ) :
    VG p (binomMoment k) 0 := by
  have h3 := inv_three_VG p hp3
  induction k with
  | zero =>
    rw [binomMoment_zero]
    simpa [div_eq_mul_inv] using h3.neg
  | succ k ih =>
    have he : binomMoment (k+1) = (-binomMoment k - (binomPoly (k+1)).eval 1) * (3:ℚ)⁻¹ := by
      have := binomMoment_succ k
      field_simp
      linarith
    have hv : VG p ((binomPoly (k+1)).eval 1) 0 := by
      simpa using binomPoly_eval_int_VG p (k+1) 1
    rw [he]
    simpa using (ih.neg.sub hv).mul h3

/-- For p != 3: values of g at 0..d with v_p >= r give v_p(G g) >= r. -/
theorem Gm_VG_of_ne_three (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) {g : ℚ[X]} {d : ℕ}
    (hg : g.natDegree ≤ d) (r : ℚ) (hv : ∀ i ≤ d, VG p (g.eval (i:ℚ)) r) : VG p (Gm g) r := by
  rw [Gm_newton hg]
  apply VG.sum
  intro k hk
  have hk' : k ≤ d := by simp at hk; omega
  have hc := newtonCoeff_VG p 0 r k (fun i hi => by simpa using hv i (hi.trans hk'))
  simpa using hc.mul (binomMoment_VG_of_ne_three p hp3 k)

end
end Li2

end
