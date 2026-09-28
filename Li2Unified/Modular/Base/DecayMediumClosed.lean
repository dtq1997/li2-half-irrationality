module
public import Li2Unified.Modular.Base.DecayMediumAssembly

set_option backward.privateInPublic true

@[expose] public section

/-! the normalisation.
Class c (elements c+1+pm <= 4n) has C = Ccl p (4n) c elements and N = Ncl p n c of them <= n.
Every surviving node has weight >= W c = 3N - C - 1 + [p | c+1], so for p prime, p != 2,3,
4n < p^2:
  v_p(Qtilde n) >= sum_c sum_{k < C-N} min(W c + 2k, 0)
                  + 2n((4n)/p - 3(n/p)) - 2 sum_{i<2n} i/p. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

def Ncl (p n c : ℕ) : ℕ := if c + 1 ≤ n then (n - (c+1))/p + 1 else 0

def Wcl (p n c : ℕ) : ℚ :=
  3 * (Ncl p n c : ℚ) - (Ccl p (4*n) c : ℚ) - 1 + (if p ∣ c + 1 then 1 else 0)

/-- x/p = q from q*p <= x < (q+1)*p, with the products generalised away. -/
lemma div_eq_of_bounds {x p q : ℕ} (h1 : q * p ≤ x) (h2 : x < (q+1) * p) : x / p = q :=
  Nat.div_eq_of_lt_le h1 h2

lemma Ccl_spec {p K c : ℕ} (hp : 0 < p) (hc : c + 1 ≤ K) :
    (Ccl p K c - 1) * p ≤ K - (c+1) ∧ K - (c+1) < Ccl p K c * p := by
  have hC : Ccl p K c = (K - (c+1))/p + 1 := by simp [Ccl, hc]
  rw [hC, Nat.add_sub_cancel]
  exact ⟨Nat.div_mul_le_self _ _, by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hp⟩

lemma Ncl_spec {p n c : ℕ} (hp : 0 < p) (hc : c + 1 ≤ n) :
    (Ncl p n c - 1) * p ≤ n - (c+1) ∧ n - (c+1) < Ncl p n c * p := by
  have hN : Ncl p n c = (n - (c+1))/p + 1 := by simp [Ncl, hc]
  rw [hN, Nat.add_sub_cancel]
  exact ⟨Nat.div_mul_le_self _ _, by rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hp⟩

lemma Ncl_le_Ccl {p n c : ℕ} (hp : 0 < p) : Ncl p n c ≤ Ccl p (4*n) c := by
  unfold Ncl Ccl
  split_ifs with h1 h2
  · exact Nat.succ_le_succ (Nat.div_le_div_right (by omega))
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

/-- Surviving nodes: position m = C-1-k >= N, i.e. jn > n, with weight >= Wcl. -/
theorem wv_jn_ge {p n c k : ℕ} (hp : 0 < p) (hc : c < p) (hk : k < Ccl p (4*n) c - Ncl p n c) :
    n < jn p (4*n) c k ∧ Wcl p n c ≤ wv n p (jn p (4*n) c k) := by
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
  refine ⟨hj ▸ hjn, ?_⟩
  rw [hj]
  unfold wv
  rw [if_neg (by omega)]
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
  have hpj : (if p ≤ c + 1 + p*m then (2:ℚ) else 0) ≤ 2 := by split_ifs <;> norm_num
  linarith

/-- The per-class lower bound. -/
theorem class_sum_ge {p n c : ℕ} (hp : 0 < p) (hc : c < p) :
    ∑ k ∈ Finset.range (Ncl p n c), (0:ℚ) +
      ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (Wcl p n c + 2 * k) 0 ≤
    ∑ k ∈ Finset.range (Ccl p (4*n) c), min (wv n p (jn p (4*n) c k) + 2 * k) 0 := by
  have hNC := Ncl_le_Ccl (p := p) (n := n) (c := c) hp
  rw [Finset.sum_const_zero, zero_add,
    ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le (Ccl p (4*n) c) (Ncl p n c))]
  have h1 : ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (Wcl p n c + 2 * k) 0 ≤
      ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c), min (wv n p (jn p (4*n) c k) + 2 * k) 0 :=
    Finset.sum_le_sum fun k hk => min_le_min_right _ (by
      linarith [(wv_jn_ge hp hc (Finset.mem_range.mp hk)).2])
  have h2 : 0 ≤ ∑ k ∈ Finset.Ico (Ccl p (4*n) c - Ncl p n c) (Ccl p (4*n) c),
      min (wv n p (jn p (4*n) c k) + 2 * k) 0 := by
    apply Finset.sum_nonneg
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    have hcK := Ccl_pos p (4*n) hk2
    -- cancelled node: jn <= n
    have hjn : jn p (4*n) c k ≤ n := by
      have hcn : c + 1 ≤ n := by
        by_contra h
        have : Ncl p n c = 0 := by simp [Ncl, h]
        omega
      obtain ⟨hN1, hN2⟩ := Ncl_spec hp hcn
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

/-! ## The exact valuation of the normalisation -/

lemma padicValRat_prod_range (p : ℕ) [Fact p.Prime] (f : ℕ → ℚ) (hf : ∀ i, f i ≠ 0) (N : ℕ) :
    padicValRat p (∏ i ∈ Finset.range N, f i) = ∑ i ∈ Finset.range N, padicValRat p (f i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      padicValRat.mul (Finset.prod_ne_zero_iff.mpr fun i _ => hf i) (hf N), ih]

def normVal (p n : ℕ) : ℚ :=
  2 * (n:ℚ) * (((4*n)/p : ℕ) - 3 * ((n/p : ℕ) : ℚ)) -
    2 * ∑ i ∈ Finset.range (2*n), ((i/p : ℕ) : ℚ)

theorem normScale_val (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hK : 4*n < p^2) :
    padicValRat p (Sn n ^ (2*n) / Fn n) = normVal p n := by
  have hf : ∀ m : ℕ, (m.factorial : ℚ) ≠ 0 := fun m => by positivity
  have hS : Sn n ≠ 0 := (Sn_pos n).ne'
  have hF : Fn n ≠ 0 := (Fn_pos n).ne'
  rw [padicValRat.div (pow_ne_zero _ hS) hF, padicValRat.pow, Sn,
    padicValRat.div (hf _) (pow_ne_zero _ (hf _)), padicValRat.pow,
    padicValRat_factorial_small p hK, padicValRat_factorial_small p (by omega : n < p^2)]
  have hFv : padicValRat p (Fn n) = 2 * ∑ i ∈ Finset.range (2*n), ((i/p : ℕ) : ℤ) := by
    unfold Fn
    rw [padicValRat_prod_range p _ (fun i => pow_ne_zero _ (hf i)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [padicValRat.pow, padicValRat_factorial_small p (by
      have := Finset.mem_range.mp hi; omega)]
    ring
  rw [hFv, normVal]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Int.cast_sum,
    Nat.cast_mul, Nat.cast_ofNat]

end
end Li2

end
