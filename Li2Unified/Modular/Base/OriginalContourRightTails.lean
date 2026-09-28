module
public import Li2Unified.Modular.Base.OriginalContourResidue
public import Li2Unified.Modular.Base.OriginalContourIBP
public import Mathlib.Analysis.SpecificLimits.Normed

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace Li2
noncomputable section

lemma originalContourPower_nat_add (N : ℕ) (z : ℂ) :
    originalContourPower ((N : ℂ) + z) =
      (1 / 2 : ℂ) ^ N * originalContourPower z := by
  calc
    originalContourPower ((N : ℂ) + z) =
        originalContourPower (N : ℂ) * originalContourPower z := by
      simp only [originalContourPower, mul_add, Complex.exp_add]
    _ = (1 / 2 : ℂ) ^ N * originalContourPower z := by
      rw [originalContourPower_nat]

lemma originalRightDecay_tendsto_zero (d : ℕ) :
    Tendsto (fun N : ℕ =>
      (1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
  have hs :=
    (summable_pow_mul_geometric_of_norm_lt_one d
      (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_atTop_zero
  have ht :
      Tendsto (fun N : ℕ =>
        ((N + 1 : ℕ) : ℝ) ^ d * (1 / 2 : ℝ) ^ (N + 1))
        atTop (𝓝 0) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have heq :
      (fun N : ℕ => (1 + (N : ℝ)) ^ d * (1 / 2 : ℝ) ^ N) =
      (fun N : ℕ =>
        2 * (((N + 1 : ℕ) : ℝ) ^ d *
          (1 / 2 : ℝ) ^ (N + 1))) := by
    funext N
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  rw [heq]
  simpa only [mul_zero] using ht.const_mul 2

end
end Li2

end
