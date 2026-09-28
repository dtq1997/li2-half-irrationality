module
public import Li2Unified.Modular.Base.DecayResidue

set_option backward.privateInPublic true

@[expose] public section

/-! the simple-pole value j(-2)^j(X - tau_j) is
split into a Y=X+Cst part and finite sums over reflected nodes m.
With Cst K = sum_{a=1}^K (-2)^a/a^2 and 1<=j<=K,
  j(-2)^j (tau_j + Cst K) = sum_{m < j+K+1} j(-2)^m/(j-m)^2,
where the m=j summand is j(-2)^j/0 = 0 in Lean. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def Cst (K : ℕ) : ℚ := ∑ a ∈ Finset.Icc 1 K, (-2:ℚ)^a / ((a:ℚ))^2

/-- The summand j(-2)^m/(j-m)^2; zero on the diagonal. -/
def poleNode (j m : ℕ) : ℚ := (j:ℚ) * (-2:ℚ)^m / (((j:ℚ) - m))^2

lemma poleNode_self (j : ℕ) : poleNode j j = 0 := by simp [poleNode]

lemma sum_Icc_one_eq_range (f : ℕ → ℚ) (j : ℕ) :
    ∑ a ∈ Finset.Icc 1 j, f a = ∑ k ∈ Finset.range j, f (k+1) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma tau_node (j : ℕ) :
    (j:ℚ) * (-2:ℚ)^j * tau j = ∑ m ∈ Finset.range j, poleNode j m := by
  unfold tau
  rw [sum_Icc_one_eq_range, Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < j := Finset.mem_range.mp hk
  unfold poleNode
  have e1 : j - 1 - k + 1 = j - k := by omega
  rw [e1]
  have e2 : (-2:ℚ)^j * (-1/2:ℚ)^(j-k) = (-2:ℚ)^k := by
    have : (-1/2:ℚ) = ((-2:ℚ))⁻¹ := by norm_num
    rw [this, inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ (by norm_num)), ← pow_add]
    congr 1; omega
  have e3 : ((j - k : ℕ) : ℚ) = (j:ℚ) - k := by rw [Nat.cast_sub hk'.le]
  rw [e3]
  calc (j:ℚ) * (-2:ℚ)^j * ((-1/2:ℚ)^(j-k) / ((j:ℚ) - k)^2)
      = (j:ℚ) * ((-2:ℚ)^j * (-1/2:ℚ)^(j-k)) / ((j:ℚ) - k)^2 := by ring
    _ = (j:ℚ) * (-2:ℚ)^k / ((j:ℚ) - k)^2 := by rw [e2]

lemma Cst_node (K j : ℕ) :
    (j:ℚ) * (-2:ℚ)^j * Cst K = ∑ m ∈ Finset.Ico (j+1) (j+K+1), poleNode j m := by
  unfold Cst
  rw [sum_Icc_one_eq_range, Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
    show j + K + 1 - (j+1) = K by omega]
  apply Finset.sum_congr rfl
  intro k _
  unfold poleNode
  have e : ((j + 1 + k : ℕ) : ℚ) = (j:ℚ) + ((k:ℚ)+1) := by push_cast; ring
  rw [e, show j + 1 + k = j + (k+1) by ring, pow_add]
  have : ((j:ℚ) - ((j:ℚ) + ((k:ℚ)+1)))^2 = (((k+1:ℕ):ℚ))^2 := by push_cast; ring
  rw [this]
  ring

theorem pole_split (K j : ℕ) :
    (j:ℚ) * (-2:ℚ)^j * (tau j + Cst K) = ∑ m ∈ Finset.range (j+K+1), poleNode j m := by
  rw [mul_add, tau_node, Cst_node, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le j) (by omega : j ≤ j+K+1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : j < j+K+1), poleNode_self, zero_add]

lemma Cst_VG (p : ℕ) [Fact p.Prime] {K N : ℕ} (hKN : K ≤ N) :
    VG p (Cst K) (-2 * (Nat.log p N : ℚ)) := by
  unfold Cst
  apply VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  have h1 : VG p ((-2:ℚ)^a) 0 := by
    have : ((-2:ℚ)^a) = (((-2:ℤ)^a : ℤ) : ℚ) := by push_cast; ring
    rw [this]; exact VG.intCast _
  have h2 := VG.inv_nat (p := p) (j := a) (n := N) ha1 (ha2.trans hKN)
  have h3 : VG p (((a:ℚ)^2)⁻¹) (2 * -(Nat.log p N : ℚ)) := by
    rw [← inv_pow]; exact_mod_cast h2.pow 2
  rw [div_eq_mul_inv]
  refine (h1.mul h3).mono ?_
  linarith

lemma poleNode_VG (p : ℕ) [Fact p.Prime] {j m N : ℕ} (hjm : j ≠ m)
    (hN : j - m ≤ N ∧ m - j ≤ N) :
    VG p (poleNode j m) ((m:ℚ) * (padicValRat p (-2) : ℚ) - 2 * (Nat.log p N : ℚ)) := by
  unfold poleNode
  have hd : ((j:ℚ) - m)^2 = ((((j - m : ℕ) + (m - j : ℕ) : ℕ) : ℚ))^2 := by
    rcases le_total j m with h | h
    · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h]; ring
    · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h]
  set t := (j - m : ℕ) + (m - j : ℕ) with ht
  have ht1 : 1 ≤ t := by omega
  have htN : t ≤ N := by omega
  rw [hd, div_eq_mul_inv]
  have h2 := VG.inv_nat (p := p) (j := t) (n := N) ht1 htN
  have h3 : VG p (((t:ℚ)^2)⁻¹) (2 * -(Nat.log p N : ℚ)) := by
    rw [← inv_pow]; exact_mod_cast h2.pow 2
  have hpow : VG p ((-2:ℚ)^m) ((m:ℚ) * (padicValRat p (-2) : ℚ)) := by
    right
    rw [padicValRat.pow (by norm_num)]
    push_cast; rfl
  refine (((VG.natCast (p := p) j).mul hpow).mul h3).mono ?_
  linarith

end
end Li2

end
