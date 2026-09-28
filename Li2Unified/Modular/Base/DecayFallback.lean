module
public import Li2Unified.Modular.Base.DecayReflect
public import Li2Unified.Modular.Base.DecayThreeAdic

set_option backward.privateInPublic true

@[expose] public section

/-! the fallback bound at every prime p != 2,3 (no p^2 > 4n needed):
v_p(Qtilde n) >= -4n log_p(7n-2), n >= 1. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

theorem binomGram_entry_GV_fallback (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {n : ℕ} (hn : 1 ≤ n) {a b : ℕ} (ha : a < 2*n) (hb : b < 2*n) :
    GV p (numeratorFunctional (4*n) (gramNum n a b)) (-2 * (Nat.log p (7*n-2) : ℚ)) := by
  set L := (Nat.log p (7*n-2) : ℚ) with hL
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have l1 : (Nat.log p (3*n+a+b) : ℚ) ≤ L := by
    rw [hL]; exact_mod_cast Nat.log_mono_right (by omega)
  have l2 : (Nat.log p (3*n+a+b-4*n) : ℚ) ≤ L := by
    rw [hL]; exact_mod_cast Nat.log_mono_right (by omega)
  unfold numeratorFunctional
  apply GV.add
  · apply GV.C
    rw [polynomialMoment_eq_Gm]
    set q := gramNum n a b /ₘ D (4*n)
    have hq : q.natDegree ≤ 3*n+a+b-4*n := gramQuot_natDegree_le n a b
    have hdeg : (derivative (X * q)).natDegree ≤ 3*n+a+b-4*n := by
      refine (natDegree_derivative_le _).trans ?_
      have := natDegree_mul_le (p := (X:ℚ[X])) (q := q)
      rw [natDegree_X] at this
      omega
    apply Gm_VG_of_ne_three p hp3 hdeg
    intro i _
    have hv := gramQuot_eval_VG p n a b (i : ℤ)
    have hd := derivative_eval_VG p hq _ (gramQuot_eval_VG p n a b) (i : ℤ)
    push_cast at hv hd
    rw [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X]
    refine (hv.mono (by linarith)).add (((VG.natCast (p := p) i).mul hd).mono ?_)
    linarith
  · apply GV.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : VG p ((gramNum n a b).eval (-(j:ℚ)) /
        ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))) 0 := gramRes_VG p n a b hj1 hj2
    have hc : VG p ((j:ℚ)*(-2:ℚ)^j) 0 := by
      have : ((j:ℚ)*(-2:ℚ)^j) = (((j:ℤ) * (-2:ℤ)^j : ℤ) : ℚ) := by push_cast; ring
      rw [this]; exact VG.intCast _
    have ht : VG p (tau j) (-2 * L) := tau_VG_of_ne_two p hp2 (by omega : j ≤ 7*n-2)
    have hlin : GV p (X - C (tau j)) (-2 * L) := (GV.X.mono (by linarith)).sub (GV.C ht)
    refine ((GV.C hres).mul ((GV.C hc).mul hlin)).mono ?_
    linarith

theorem Qtilde_GV_fallback (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) {n : ℕ}
    (hn : 1 ≤ n) : GV p (Qtilde n) (-4 * (n:ℚ) * (Nat.log p (7*n-2) : ℚ)) := by
  set L := (Nat.log p (7*n-2) : ℚ)
  rw [Qtilde_eq_binomGram_det]
  have hdet := det_GV (p := p) (binomGram n) (fun _ => -L) (fun _ => -L) (fun a b => by
    rw [binomGram_apply]
    refine (binomGram_entry_GV_fallback p hp2 hp3 hn a.isLt b.isLt).mono (le_of_eq ?_)
    ring)
  refine hdet.mono (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end
end Li2

end
