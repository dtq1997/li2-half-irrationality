module
public import Li2Unified.Modular.Base.DecayMediumClosed

set_option backward.privateInPublic true

@[expose] public section

/-! refinement: keep the exact tau term. The slot weight is
  Wcl + 2 - 2[p <= jn c k],
so the smallest node j=c+1<p (when it survives) gets weight Wcl+2. This removes the
loss 2 (C=1 classes) and 1 (C=2 classes) in the outer window, and gives v_p >= 0 for p>4n. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def Wslot (p n c k : ℕ) : ℚ :=
  Wcl p n c + 2 - (if p ≤ jn p (4*n) c k then 2 else 0)

theorem wv_jn_ge' {p n c k : ℕ} (hp : 0 < p) (hc : c < p) (hk : k < Ccl p (4*n) c - Ncl p n c) :
    Wcl p n c + 2 - (if p ≤ jn p (4*n) c k then 2 else 0) ≤ wv n p (jn p (4*n) c k) := by
  have hkC : k < Ccl p (4*n) c := by omega
  have hcK := Ccl_pos p (4*n) hkC
  obtain ⟨hC1, hC2⟩ := Ccl_spec hp hcK
  have hj : jn p (4*n) c k = c + 1 + p * (Ccl p (4*n) c - 1 - k) := rfl
  generalize hCv : Ccl p (4*n) c = Cv at hk hkC hC1 hC2 hj
  generalize hNv : Ncl p n c = Nv at hk
  obtain ⟨m, hm⟩ : ∃ m, m = Cv - 1 - k := ⟨_, rfl⟩
  rw [← hm] at hj
  have hmN : Nv ≤ m := by omega
  have hmC : m ≤ Cv - 1 := by omega
  -- products as atoms
  have hmp1 : m * p ≤ (Cv - 1) * p := Nat.mul_le_mul_right p hmC
  have hNp : Nv * p ≤ m * p := Nat.mul_le_mul_right p hmN
  have hCm : (Cv - 1) * p + p = Cv * p := by
    rw [← Nat.succ_mul]; congr 1; omega
  have hpm : p * m = m * p := mul_comm p m
  -- j > n
  have hcn_or : c + 1 ≤ n → n - (c+1) < Nv * p := by
    intro hcn
    have := (Ncl_spec hp hcn).2
    rwa [hNv] at this
  have hcn_or1 : c + 1 ≤ n → (Nv - 1) * p ≤ n - (c+1) := by
    intro hcn
    have := (Ncl_spec hp hcn).1
    rwa [hNv] at this
  have hN0 : ¬ c + 1 ≤ n → Nv = 0 := fun h => by rw [← hNv]; simp [Ncl, h]
  have hjn : n < c + 1 + p * m := by
    rw [hpm]
    by_cases hcn : c + 1 ≤ n
    · have := hcn_or hcn; omega
    · omega
  rw [hj]
  unfold wv
  rw [if_neg (show ¬ (c + 1 + p*m ≤ n) by omega)]
  have f1 : (c + 1 + p*m - 1)/p = m := by
    rw [show c + 1 + p*m - 1 = c + p*m by omega, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hc,
      zero_add]
  have f3 : (4*n - (c + 1 + p*m))/p = Cv - 1 - m := by
    apply div_eq_of_bounds
    · rw [Nat.sub_mul, hpm]
      generalize (Cv - 1) * p = A at hmp1 hC1 hCm ⊢
      generalize m * p = B at hmp1 hNp ⊢
      omega
    · rw [show Cv - 1 - m + 1 = Cv - m by omega, Nat.sub_mul, hpm]
      generalize (Cv - 1) * p = A at hmp1 hC1 hCm ⊢
      generalize m * p = B at hmp1 hNp ⊢
      generalize Cv * p = D at hC2 hCm ⊢
      omega
  have f2 : ((c + 1 + p*m - 1 - n)/p : ℕ) ≤ m - Nv := by
    by_cases hcn : c + 1 ≤ n
    · have h1 := hcn_or1 hcn
      have h2 := hcn_or hcn
      have hN1 : 1 ≤ Nv := by
        rcases Nat.eq_zero_or_pos Nv with h | h
        · rw [h, zero_mul] at h2; omega
        · exact h
      have hNN : (Nv - 1) * p + p = Nv * p := by
        rw [← Nat.succ_mul]; congr 1; omega
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      rw [Nat.succ_mul, Nat.sub_mul, hpm]
      generalize m * p = B at hNp ⊢
      generalize (Nv - 1) * p = E' at h1 hNN
      generalize Nv * p = E at hNp h2 hNN ⊢
      omega
    · rw [hN0 hcn, Nat.sub_zero]
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hp).mpr
      rw [Nat.succ_mul, hpm]
      generalize m * p = B
      omega
  have hdv : (if p ∣ c + 1 + p*m then (1:ℚ) else 0) = (if p ∣ c + 1 then 1 else 0) := by
    by_cases h : p ∣ c + 1
    · rw [if_pos h, if_pos (dvd_add h (dvd_mul_right p m))]
    · rw [if_neg h, if_neg (fun h' => h ((Nat.dvd_add_left (dvd_mul_right p m)).mp h'))]
  rw [f1, f3, hdv]
  unfold Wcl
  rw [hCv, hNv]
  have hf2 : ((((c + 1 + p*m - 1 - n)/p : ℕ)) : ℚ) ≤ (m:ℚ) - Nv := by
    have := (Nat.cast_le (α := ℚ)).mpr f2
    rwa [Nat.cast_sub hmN] at this
  have hC' : ((Cv - 1 - m : ℕ) : ℚ) = (Cv:ℚ) - 1 - m := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [hC']
  linarith

theorem class_sum_ge' {p n c : ℕ} (hp : 0 < p) (hc : c < p) :
    ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (Wslot p n c k + 2 * k) 0 ≤
    ∑ k ∈ Finset.range (Ccl p (4*n) c), min (wv n p (jn p (4*n) c k) + 2 * k) 0 := by
  have h := class_sum_ge (p := p) (n := n) (c := c) hp hc
  have hNC := Ncl_le_Ccl (p := p) (n := n) (c := c) hp
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le (Ccl p (4*n) c) (Ncl p n c))]
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le (Ccl p (4*n) c) (Ncl p n c))] at h
  simp only [Finset.sum_const_zero, zero_add] at h
  have h1 : ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (Wslot p n c k + 2 * k) 0 ≤
      ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (wv n p (jn p (4*n) c k) + 2 * k) 0 :=
    Finset.sum_le_sum fun k hk => min_le_min_right _ (by
      have := wv_jn_ge' (n := n) hp hc (Finset.mem_range.mp hk)
      unfold Wslot; linarith)
  have h2 : 0 ≤ ∑ k ∈ Finset.Ico (Ccl p (4*n) c - Ncl p n c) (Ccl p (4*n) c),
      min (wv n p (jn p (4*n) c k) + 2 * k) 0 := by
    have hlo : ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (Wcl p n c + 2 * k) 0 ≤
        ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (wv n p (jn p (4*n) c k) + 2 * k) 0 :=
      Finset.sum_le_sum fun k hk => min_le_min_right _ (by
        linarith [(wv_jn_ge hp hc (Finset.mem_range.mp hk)).2])
    apply Finset.sum_nonneg
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have hcn : c + 1 ≤ n := by
      by_contra h'
      have : Ncl p n c = 0 := by simp [Ncl, h']
      omega
    obtain ⟨hN1, hN2⟩ := Ncl_spec hp hcn
    have hjn : jn p (4*n) c k ≤ n := by
      unfold jn
      have hm : Ccl p (4*n) c - 1 - k ≤ Ncl p n c - 1 := by omega
      have := Nat.mul_le_mul_right p hm
      rw [mul_comm p]
      generalize (Ccl p (4*n) c - 1 - k) * p = A at this ⊢
      generalize (Ncl p n c - 1) * p = B at this hN1 ⊢
      omega
    simp only [wv, if_pos hjn]
    apply le_min
    · positivity
    · exact le_rfl
  linarith

end
end Li2

end
