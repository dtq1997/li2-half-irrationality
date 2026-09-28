module
public import Li2Unified.Modular.Base.DecayMediumNodes
public import Li2Unified.Modular.Base.DecayRankOne
public import Li2Unified.Modular.Base.IntegerFamily

set_option backward.privateInPublic true

@[expose] public section

/-! every prime p >= 5 with 4n < p^2, applied to the SAME Q n.
The poles j in [1,4n] are regrouped by c = (j-1) mod p, each class listed in decreasing j.
The weight of node j is (j <= n: cancelled, gamma_j = 0, weight 4K+4) or
  2((j-1)/p) - 3((j-1-n)/p) - (K-j)/p + [p | j] - 2[p <= j],
which is nondecreasing along the class. rank_one_GV then gives
  v_p(Q n) >= sum_c sum_{k < Cc c} min(w(jn c k) + 2k, 0). -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

section Regroup
variable (p K : ℕ)

def Ccl (c : ℕ) : ℕ := if c + 1 ≤ K then (K - (c+1))/p + 1 else 0

def jn (c t : ℕ) : ℕ := c + 1 + p * (Ccl p K c - 1 - t)

lemma Ccl_pos {c : ℕ} {t : ℕ} (ht : t < Ccl p K c) : c + 1 ≤ K := by
  unfold Ccl at ht; split_ifs at ht with h
  · exact h
  · omega

lemma jn_le {c t : ℕ} (hp : 0 < p) (ht : t < Ccl p K c) : jn p K c t ≤ K := by
  have hc := Ccl_pos p K ht
  have hC : Ccl p K c = (K - (c+1))/p + 1 := by simp [Ccl, hc]
  unfold jn
  have h2 : p * ((K - (c+1))/p) ≤ K - (c+1) := Nat.mul_div_le _ _
  generalize (K - (c+1))/p = g at hC h2
  have h1 : Ccl p K c - 1 - t ≤ g := by omega
  have h3 := Nat.mul_le_mul_left p h1
  omega

lemma regroup_aux {j : ℕ} (hp : 0 < p) (hj1 : 1 ≤ j) (hj2 : j ≤ K) :
    (j-1) % p < p ∧ (j-1)/p < Ccl p K ((j-1) % p) ∧
      jn p K ((j-1) % p) (Ccl p K ((j-1) % p) - 1 - (j-1)/p) = j := by
  have hdm := Nat.div_add_mod (j-1) p
  have hr := Nat.mod_lt (j-1) hp
  generalize (j-1) % p = r at hdm hr ⊢
  generalize hq : (j-1)/p = q at hdm ⊢
  generalize hP : p * q = P at hdm
  have hc : r + 1 ≤ K := by omega
  have hC : Ccl p K r = (K - (r+1))/p + 1 := by simp [Ccl, hc]
  have hqg : q ≤ (K - (r+1))/p := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    rw [mul_comm, hP]; omega
  generalize (K - (r+1))/p = g at hC hqg
  refine ⟨hr, by omega, ?_⟩
  unfold jn
  rw [hC, show g + 1 - 1 - (g + 1 - 1 - q) = q by omega, hP]
  omega

lemma regroup_inv {c t : ℕ} (hp : 0 < p) (hc : c < p) (ht : t < Ccl p K c) :
    (jn p K c t - 1) % p = c ∧ (jn p K c t - 1) / p = Ccl p K c - 1 - t := by
  have e : jn p K c t - 1 = c + p * (Ccl p K c - 1 - t) := by unfold jn; omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, Nat.add_mul_div_left _ _ hp,
    Nat.div_eq_of_lt hc, zero_add]
  exact ⟨rfl, rfl⟩

theorem regroup {R : Type*} [AddCommMonoid R] (hp : 0 < p) (F : ℕ → R) :
    ∑ j ∈ Finset.Icc 1 K, F j =
      ∑ c ∈ Finset.range p, ∑ t ∈ Finset.range (Ccl p K c), F (jn p K c t) := by
  rw [← Finset.sum_sigma (Finset.range p) (fun c => Finset.range (Ccl p K c))
    (fun x => F (jn p K x.1 x.2))]
  refine Finset.sum_bij' (fun j _ => ⟨(j-1) % p, Ccl p K ((j-1) % p) - 1 - (j-1)/p⟩)
    (fun x _ => jn p K x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    obtain ⟨h1, h2, -⟩ := regroup_aux p K hp hj1 hj2
    simp only [Finset.mem_sigma, Finset.mem_range]
    refine ⟨h1, ?_⟩
    generalize Ccl p K ((j-1) % p) = Cv at h2 ⊢
    generalize (j-1)/p = q at h2 ⊢
    omega
  · rintro ⟨c, t⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only [Finset.mem_Icc]
    exact ⟨by unfold jn; omega, jn_le p K hp hx.2⟩
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    exact (regroup_aux p K hp hj1 hj2).2.2
  · rintro ⟨c, t⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨hmod, hdiv⟩ := regroup_inv p K hp hx.1 hx.2
    simp only [hmod, hdiv]
    congr 1
    omega
  · intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    rw [(regroup_aux p K hp hj1 hj2).2.2]

end Regroup

/-! ## Node weights -/

def wv (n p j : ℕ) : ℚ :=
  if j ≤ n then (4*(4*n) : ℚ) + 4 else
    (2 * ((j-1)/p : ℕ) - 3 * ((j-1-n)/p : ℕ) - ((4*n-j)/p : ℕ) : ℚ) +
      (if p ∣ j then 1 else 0) - (if p ≤ j then 2 else 0)

lemma wv_le_big {n p j : ℕ} (hj : j ≤ 4*n) : wv n p j ≤ (4*(4*n) : ℚ) + 4 := by
  unfold wv
  split_ifs <;> (
    have h1 : (((j-1)/p : ℕ) : ℚ) ≤ 4*n := by exact_mod_cast (Nat.div_le_self _ _).trans (by omega)
    have h2 : (0:ℚ) ≤ ((j-1-n)/p : ℕ) := Nat.cast_nonneg _
    have h3 : (0:ℚ) ≤ ((4*n-j)/p : ℕ) := Nat.cast_nonneg _
    linarith) <;> linarith

lemma wv_step {n p j d : ℕ} (hp : 0 < p) (hnj : n < j) (hK : j + p*d ≤ 4*n) :
    wv n p (j + p*d) ≤ wv n p j := by
  unfold wv
  rw [if_neg (show ¬ (j + p*d ≤ n) by omega), if_neg (show ¬ (j ≤ n) by omega)]
  have e1 : (j + p*d - 1)/p = (j-1)/p + d := by
    rw [show j + p*d - 1 = (j-1) + p*d by omega, Nat.add_mul_div_left _ _ hp]
  have e2 : (j + p*d - 1 - n)/p = (j-1-n)/p + d := by
    rw [show j + p*d - 1 - n = (j-1-n) + p*d by omega, Nat.add_mul_div_left _ _ hp]
  have e3 : (4*n - j)/p = (4*n - (j + p*d))/p + d := by
    rw [show 4*n - j = (4*n - (j + p*d)) + p*d by omega, Nat.add_mul_div_left _ _ hp]
  rw [e1, e2, e3]
  have hle : (if p ≤ j then (2:ℚ) else 0) ≤ (if p ≤ j + p*d then 2 else 0) := by
    by_cases h1 : p ≤ j
    · rw [if_pos h1, if_pos (le_trans h1 (Nat.le_add_right _ _))]
    · rw [if_neg h1]; split_ifs <;> norm_num
  have hd : (if p ∣ j + p*d then (1:ℚ) else 0) = (if p ∣ j then 1 else 0) := by
    by_cases h : p ∣ j
    · rw [if_pos h, if_pos (dvd_add h (dvd_mul_right p d))]
    · rw [if_neg h, if_neg (fun h' => h ((Nat.dvd_add_left (dvd_mul_right p d)).mp h'))]
  rw [hd]
  push_cast
  linarith

/-! ## The literal pole scalars -/

lemma nat_VG_dvd (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj : 0 < j) :
    VG p (j:ℚ) (if p ∣ j then 1 else 0) := by
  split_ifs with h
  · right
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd (by omega) h
  · exact VG.natCast j

/-! ## The raw determinant as W + rank-one sum -/

end
end Li2

end
