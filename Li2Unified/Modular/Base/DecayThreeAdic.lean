module
public import Li2Unified.Modular.Base.DecayResidue

set_option backward.privateInPublic true

@[expose] public section

/-! the 3-adic bound for the SAME Qtilde n = S_n^(2n)/F_n Q_n.
With L = Nat.log 3 (7n-2) and S3 n = sum_{a<2n} (2a+1-n)^+ (so 4 S3 n + n%2 = 9n^2),
for every n>=1, every coefficient of Qtilde n has v_3 >= -S3 n - 4nL. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

lemma inv_two_VG (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : VG p (2 : ℚ)⁻¹ 0 := by
  have hn : ¬p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out (by decide)).mp h)
  have hv : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
    rfl
  right
  rw [padicValRat.inv, hv]
  norm_num

lemma tau_VG_of_ne_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {j N : ℕ} (hjN : j ≤ N) :
    VG p (tau j) (-2 * (Nat.log p N : ℚ)) := by
  unfold tau
  apply VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have h1 : VG p ((-1/2 : ℚ)^a) 0 := by
    have : (-1/2 : ℚ) = (-1) * (2:ℚ)⁻¹ := by ring
    rw [this]
    have h := ((VG.one (p := p)).neg.mul (inv_two_VG p hp2)).pow a
    simpa using h
  have h2 := VG.inv_nat (p := p) (j := a) (n := N) ha1 (ha2.trans hjN)
  have h3 : VG p (((a:ℚ)^2)⁻¹) (2 * -(Nat.log p N : ℚ)) := by
    rw [← inv_pow]; exact_mod_cast h2.pow 2
  rw [div_eq_mul_inv]
  refine (h1.mul h3).mono ?_
  linarith

/-- binomGram entries are the literal functional applied to gramNum. -/
lemma binomGram_apply (n : ℕ) (a b : Fin (2*n)) :
    binomGram n a b = numeratorFunctional (4*n) (gramNum n a b) := rfl

theorem gramQuot_eq_zero {n a b : ℕ} (h : a + b < n) : gramNum n a b /ₘ D (4*n) = 0 := by
  rw [gramNum_divByMonic]
  apply Finset.sum_eq_zero
  intro k hk
  exfalso
  simp at hk
  omega

/-- Entry bound at 3: v_3 >= -(a+b+1-n)^+ - 2L. -/
theorem binomGram_entry_GV_three {n : ℕ} (hn : 1 ≤ n) {a b : ℕ} (ha : a < 2*n) (hb : b < 2*n) :
    GV 3 (numeratorFunctional (4*n) (gramNum n a b))
      (-((a+b+1-n : ℕ) : ℚ) - 2 * (Nat.log 3 (7*n-2) : ℚ)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  set L := (Nat.log 3 (7*n-2) : ℚ) with hL
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hφ : (0:ℚ) ≤ ((a+b+1-n : ℕ) : ℚ) := Nat.cast_nonneg _
  unfold numeratorFunctional
  apply GV.add
  · apply GV.C
    by_cases hab : a + b < n
    · rw [gramQuot_eq_zero hab]
      simp [polynomialMoment, VG.zero]
    · have hU := polynomialMoment_VG_three (gramQuot_natDegree_le n a b)
        (-(Nat.log 3 (3*n+a+b) : ℚ)) (gramQuot_eval_VG 3 n a b)
      refine hU.mono ?_
      have e1 : (Nat.log 3 (3*n+a+b) : ℚ) ≤ L := by
        rw [hL]; exact_mod_cast Nat.log_mono_right (by omega)
      have e2 : (Nat.log 3 (3*n+a+b-4*n) : ℚ) ≤ L := by
        rw [hL]; exact_mod_cast Nat.log_mono_right (by omega)
      have e3 : ((3*n+a+b-4*n : ℕ) : ℚ) + 1 = ((a+b+1-n : ℕ) : ℚ) := by
        rw [show 3*n+a+b-4*n = a+b-n by omega, show a+b+1-n = (a+b-n)+1 by omega]
        push_cast; ring
      linarith
  · apply GV.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : VG 3 ((gramNum n a b).eval (-(j:ℚ)) /
        ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))) 0 := gramRes_VG 3 n a b hj1 hj2
    have hc : VG 3 ((j:ℚ)*(-2:ℚ)^j) 0 := by
      have : ((j:ℚ)*(-2:ℚ)^j) = (((j:ℤ) * (-2:ℤ)^j : ℤ) : ℚ) := by push_cast; ring
      rw [this]; exact VG.intCast _
    have ht : VG 3 (tau j) (-2 * L) := tau_VG_of_ne_two 3 (by decide) (by omega : j ≤ 7*n-2)
    have hlin : GV 3 (X - C (tau j)) (-2 * L) :=
      (GV.X.mono (by linarith)).sub (GV.C ht)
    refine ((GV.C hres).mul ((GV.C hc).mul hlin)).mono ?_
    linarith

def S3 (n : ℕ) : ℕ := ∑ a ∈ Finset.range (2*n), (2*a+1-n)

lemma S3_add_two (n : ℕ) : S3 (n+2) = S3 n + 9*n + 9 := by
  unfold S3
  rw [show 2*(n+2) = (2*n+3) + 1 by ring, Finset.sum_range_succ', show 2*n+3 = 2*n + 3 by rfl]
  rw [Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  have hshift : ∑ x ∈ Finset.range (2*n), (2*(x+1)+1-(n+2)) = ∑ x ∈ Finset.range (2*n), (2*x+1-n) :=
    Finset.sum_congr rfl fun x _ => by omega
  rw [hshift]
  omega

theorem S3_closed (n : ℕ) : 4 * S3 n + n % 2 = 9 * n^2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [S3]
    | 1 => decide
    | m+2 =>
      rw [S3_add_two]
      have := ih m (by omega)
      have hmod : (m+2) % 2 = m % 2 := by omega
      rw [hmod]
      nlinarith

/-- The 3-adic bound on the literal Qtilde n, every n>=1. -/
theorem Qtilde_GV_three {n : ℕ} (hn : 1 ≤ n) :
    GV 3 (Qtilde n) (-(S3 n : ℚ) - 4 * (n:ℚ) * (Nat.log 3 (7*n-2) : ℚ)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  set L := (Nat.log 3 (7*n-2) : ℚ) with hL
  let ρ : Fin (2*n) → ℚ := fun a => -((2*a.val+1-n : ℕ) : ℚ)/2 - L
  rw [Qtilde_eq_binomGram_det]
  have hdet := det_GV (p := 3) (binomGram n) ρ ρ (fun a b => by
    rw [binomGram_apply]
    refine (binomGram_entry_GV_three hn a.isLt b.isLt).mono ?_
    simp only [ρ]
    have hc : 2 * (a.val+b.val+1-n) ≤ (2*a.val+1-n) + (2*b.val+1-n) := by omega
    have hc' : 2 * ((a.val+b.val+1-n : ℕ) : ℚ) ≤ ((2*a.val+1-n : ℕ) : ℚ) + ((2*b.val+1-n : ℕ) : ℚ) := by
      exact_mod_cast hc
    linarith)
  refine hdet.mono (le_of_eq ?_)
  have hs : ∑ x : Fin (2*n), ((2*x.val+1-n : ℕ) : ℚ) = (S3 n : ℚ) := by
    rw [S3, Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun a => ((2*a+1-n : ℕ) : ℚ))]
  have h2 : ∑ x : Fin (2*n), (-((2*x.val+1-n : ℕ) : ℚ)/2 - L) = (-1/2) * (S3 n : ℚ) - (2*n:ℕ) * L := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← hs, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [ρ]
  rw [h2]
  push_cast
  ring

end
end Li2

end
