module
public import Li2Unified.Modular.Base.RationalBaseEvaluation

set_option backward.privateInPublic true

@[expose] public section

/-! Congruence of the actual prime parameter and the rational base parameter.
The pole range is literal j < p; no denominator crossing p is allowed. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

lemma VG.mul_congr {a b c d s : ℚ} (hc : VG p c 0) (hb : VG p b 0)
    (hab : VG p (a-b) s) (hcd : VG p (c-d) s) : VG p (a*c-b*d) s := by
  have he : a*c-b*d = (a-b)*c+b*(c-d) := by ring
  rw [he]
  have hleft : VG p ((a-b)*c) s := by simpa using hab.mul hc
  have hright : VG p (b*(c-d)) s := by simpa using hb.mul hcd
  exact hleft.add hright

lemma VG.pow_congr {a b s : ℚ} (ha : VG p a 0) (hb : VG p b 0)
    (hab : VG p (a-b) s) (k : ℕ) : VG p (a^k-b^k) s := by
  induction k with
  | zero => simpa using VG.zero (p := p) s
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact VG.mul_congr ha (by simpa using hb.pow k) ih hab

lemma VG.inv_congr {a b s : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hia : VG p a⁻¹ 0) (hib : VG p b⁻¹ 0) (hab : VG p (a-b) s) :
    VG p (a⁻¹-b⁻¹) s := by
  have he : a⁻¹-b⁻¹ = -(a-b)*a⁻¹*b⁻¹ := by field_simp [ha, hb]; ring
  rw [he]
  simpa using (hab.neg.mul hia).mul hib

lemma GV.derivative {f : ℚ[X]} {s : ℚ} (hf : GV p f s) : GV p f.derivative s := by
  intro k
  rw [coeff_derivative]
  simpa [mul_comm] using (hf (k+1)).mul (VG.natCast (p := p) (k+1))

end
end Li2

end
