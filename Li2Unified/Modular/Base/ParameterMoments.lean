module
public import Li2Unified.Modular.Base.Valuation

set_option backward.privateInPublic true

@[expose] public section

/-! The geometric moment recurrence at a variable rational parameter.
This is the polynomial part needed for the p-dissection parameter z=lambda^p. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def parameterMoment (z : ℚ) : ℕ → ℚ
  | 0 => z/(1-z)
  | k+1 => z/(1-z) * (1 + ∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * parameterMoment z j.val)
termination_by k => k
decreasing_by exact j.isLt

theorem parameterMoment_VG (p : ℕ) [Fact p.Prime] (z : ℚ)
    (hz : VG p (z/(1-z)) 0) (k : ℕ) : VG p (parameterMoment z k) 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [parameterMoment] using hz
    | succ k =>
      rw [parameterMoment]
      have hs : VG p (∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * parameterMoment z j.val) 0 := by
        apply VG.sum
        intro j _
        simpa only [add_zero] using (VG.natCast (p := p) _).mul (ih j.val j.isLt)
      simpa only [add_zero] using hz.mul ((VG.one (p := p)).add hs)

theorem parameterMoment_congr (p : ℕ) [Fact p.Prime] (z w r : ℚ)
    (hz : VG p (z/(1-z)) 0) (hw : VG p (w/(1-w)) 0)
    (hzw : VG p (z/(1-z)-w/(1-w)) r) (k : ℕ) :
    VG p (parameterMoment z k - parameterMoment w k) r := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [parameterMoment] using hzw
    | succ k =>
      rw [parameterMoment, parameterMoment]
      let Sz := ∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * parameterMoment z j.val
      let Sw := ∑ j : Fin (k+1), (Nat.choose (k+1) j.val : ℚ) * parameterMoment w j.val
      have hs : VG p Sz 0 := by
        apply VG.sum
        intro j _
        simpa only [add_zero] using (VG.natCast (p := p) _).mul (parameterMoment_VG p z hz j.val)
      have hd : VG p (Sz-Sw) r := by
        dsimp only [Sz, Sw]
        rw [← Finset.sum_sub_distrib]
        apply VG.sum
        intro j _
        rw [← mul_sub]
        simpa only [zero_add] using (VG.natCast (p := p) _).mul (ih j.val j.isLt)
      have he : z/(1-z)*(1+Sz)-w/(1-w)*(1+Sw) =
          (z/(1-z)-w/(1-w))*(1+Sz) + w/(1-w)*(Sz-Sw) := by ring
      change VG p (z/(1-z)*(1+Sz)-w/(1-w)*(1+Sw)) r
      rw [he]
      have hleft := hzw.mul ((VG.one (p := p)).add hs)
      have hright := hw.mul hd
      simp only [add_zero] at hleft
      simp only [zero_add] at hright
      exact hleft.add hright

def parameterG (z : ℚ) (P : ℚ[X]) : ℚ :=
  P.sum fun k a => a * parameterMoment z k

theorem parameterG_VG (p : ℕ) [Fact p.Prime] (z r : ℚ)
    (hz : VG p (z/(1-z)) 0) (P : ℚ[X]) (hP : GV p P r) : VG p (parameterG z P) r := by
  unfold parameterG Polynomial.sum
  apply VG.sum
  intro k _
  simpa only [add_zero] using (hP k).mul (parameterMoment_VG p z hz k)

end
end Li2

end
