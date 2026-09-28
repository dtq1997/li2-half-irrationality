module
public import Li2Unified.Modular.Base.OuterClassAffine
public import Li2Unified.Modular.Base.MediumClassCounts
public import Li2Unified.Modular.Base.MediumFloorSum

set_option backward.privateInPublic true

@[expose] public section

open scoped BigOperators
namespace Li2
noncomputable section

def outerRawBound (p n : ℕ) : ℚ :=
  ∑ c : Fin p, ∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
    min (Wslot p n c k + 2*k) 0

lemma outer_sum_indicator {p r : ℕ} (hr : r ≤ p) :
    (∑ c : Fin p, if (c:ℕ) < r then (1:ℚ) else 0) = (r:ℚ) := by
  rw [Fin.sum_univ_eq_sum_range (fun c : ℕ => if c < r then (1:ℚ) else 0)]
  simpa using (sum_range_ite_lt_rat hr (1:ℚ) 0)

lemma outer_sum_zero_indicator {p : ℕ} (hp : 0 < p) :
    (∑ c : Fin p, if (c:ℕ)+1 = p then (1:ℚ) else 0) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun c : ℕ => if c+1=p then (1:ℚ) else 0)]
  calc
    (∑ c ∈ Finset.range p, if c+1 = p then (1:ℚ) else 0) =
        ∑ c ∈ Finset.range p, if c = p-1 then (1:ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      have he : c+1 = p ↔ c = p-1 := by omega
      simp only [he]
    _ = 1 := by simp [show p-1 < p by omega]

lemma outerRawBound_affine {p n r : ℕ} (hp : 0 < p) (hnp : n < p)
    (hrp : r < p) (A B C D : ℚ)
    (hpoint : ∀ c : Fin p,
      (∑ k ∈ Finset.range (Ccl p (4*n) c - Ncl p n c),
        min (Wslot p n c k + 2*k) 0) =
      A + B*(if (c:ℕ) < r then 1 else 0) + C*(if (c:ℕ) < n then 1 else 0) +
        D*(if (c:ℕ)+1 = p then 1 else 0)) :
    outerRawBound p n = A*(p:ℚ) + B*(r:ℚ) + C*(n:ℚ) + D := by
  unfold outerRawBound
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    outer_sum_indicator hrp.le, outer_sum_indicator hnp.le,
    outer_sum_zero_indicator hp, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma outerRawBound_w1 {p n : ℕ} (hnp : n < p)
    (hlo : 3*p ≤ 4*n) : outerRawBound p n = (n:ℚ) - 3*p + 2 := by
  have hp : 0 < p := by omega
  let r := 4*n-3*p
  have hK : 4*n = 3*p+r := by dsimp [r]; omega
  have hrn : r ≤ n := by dsimp [r]; omega
  have hrp : r < p := by dsimp [r]; omega
  have hs : outerRawBound p n = (-6:ℚ)*p + (-1)*(r:ℚ) + (5)*n + (2) := by
    apply outerRawBound_affine hp hnp hrp (-6) (-1) (5) (2)
    intro c
    rw [outer_class_q3 hnp c.isLt hrn (Ccl_eq_quot_rem hp c.isLt hrp hK)]
    ring
  have hKq : 4*(n:ℚ) = 3*(p:ℚ)+(r:ℚ) := by exact_mod_cast hK
  linarith

lemma outerRawBound_w2 {p n : ℕ} (hnp : n < p)
    (hlo : 4*n < 3*p) (hhi : 2*p ≤ 3*n) : outerRawBound p n = 3*(p:ℚ) - 7*n + 1 := by
  have hp : 0 < p := by omega
  let r := 4*n-2*p
  have hK : 4*n = 2*p+r := by dsimp [r]; omega
  have hnr : n ≤ r := by dsimp [r]; omega
  have hrp : r < p := by dsimp [r]; omega
  have hs : outerRawBound p n = (-3:ℚ)*p + (-3)*(r:ℚ) + (5)*n + (1) := by
    apply outerRawBound_affine hp hnp hrp (-3) (-3) (5) (1)
    intro c
    rw [outer_class_q2_above hnp c.isLt hrp hnr (Ccl_eq_quot_rem hp c.isLt hrp hK)]
    ring
  have hKq : 4*(n:ℚ) = 2*(p:ℚ)+(r:ℚ) := by exact_mod_cast hK
  linarith

lemma outerRawBound_w3 {p n : ℕ} (hnp : n < p)
    (hlo : 3*n < 2*p) (hhi : p ≤ 2*n) : outerRawBound p n = -(n:ℚ) - p + 1 := by
  have hp : 0 < p := by omega
  let r := 4*n-2*p
  have hK : 4*n = 2*p+r := by dsimp [r]; omega
  have hrn : r ≤ n := by dsimp [r]; omega
  have hrp : r < p := by dsimp [r]; omega
  have hs : outerRawBound p n = (-3:ℚ)*p + (-1)*(r:ℚ) + (3)*n + (1) := by
    apply outerRawBound_affine hp hnp hrp (-3) (-1) (3) (1)
    intro c
    rw [outer_class_q2_below hnp c.isLt hrn (Ccl_eq_quot_rem hp c.isLt hrp hK)]
    ring
  have hKq : 4*(n:ℚ) = 2*(p:ℚ)+(r:ℚ) := by exact_mod_cast hK
  linarith

lemma outerRawBound_w4 {p n : ℕ} (hnp : n < p)
    (hlo : 2*n < p) (hhi : p ≤ 3*n) : outerRawBound p n = 3*(p:ℚ) - 9*n - 1 := by
  have hp : 0 < p := by omega
  let r := 4*n-1*p
  have hK : 4*n = 1*p+r := by dsimp [r]; omega
  have hnr : n ≤ r := by dsimp [r]; omega
  have hrp : r < p := by dsimp [r]; omega
  have hs : outerRawBound p n = (0:ℚ)*p + (-3)*(r:ℚ) + (3)*n + (-1) := by
    apply outerRawBound_affine hp hnp hrp (0) (-3) (3) (-1)
    intro c
    rw [outer_class_q1_above hnp c.isLt hrp hnr (Ccl_eq_quot_rem hp c.isLt hrp hK)]
    ring
  have hKq : 4*(n:ℚ) = 1*(p:ℚ)+(r:ℚ) := by exact_mod_cast hK
  linarith

lemma outerRawBound_w5 {p n : ℕ} (hnp : n < p)
    (hlo : 3*n < p) (hhi : p ≤ 4*n) : outerRawBound p n = -1 := by
  have hp : 0 < p := by omega
  let r := 4*n-1*p
  have hK : 4*n = 1*p+r := by dsimp [r]; omega
  have hrn : r ≤ n := by dsimp [r]; omega
  have hrp : r < p := by dsimp [r]; omega
  have hs : outerRawBound p n = (0:ℚ)*p + (0)*(r:ℚ) + (0)*n + (-1) := by
    apply outerRawBound_affine hp hnp hrp (0) (0) (0) (-1)
    intro c
    rw [outer_class_q1_below hnp c.isLt hrn (Ccl_eq_quot_rem hp c.isLt hrp hK)]
    ring
  have hKq : 4*(n:ℚ) = 1*(p:ℚ)+(r:ℚ) := by exact_mod_cast hK
  linarith

lemma normVal_outer_low {p n L : ℕ} (hnp : n < p) (hpn : p ≤ 2*n)
    (hL : (4*n)/p = L) :
    normVal p n = 2*(n:ℚ)*L - 4*n + 2*p := by
  have hp : 0 < p := by omega
  have hB : (2*n)/p = 1 := div_eq_of_bounds (by omega) (by omega)
  rw [normVal_of_quotients hp (Nat.div_eq_of_lt hnp) hL hB]
  norm_num <;> ring

lemma normVal_outer_high {p n L : ℕ} (hnp : n < p) (hpn : 2*n < p)
    (hL : (4*n)/p = L) : normVal p n = 2*(n:ℚ)*L := by
  have hp : 0 < p := by omega
  rw [normVal_of_quotients hp (Nat.div_eq_of_lt hnp) hL (Nat.div_eq_of_lt hpn)]
  norm_num

lemma outer_prime_square {p n : ℕ} (hp5 : 5 ≤ p) (hnp : n < p) :
    4*n < p^2 := by
  nlinarith [Nat.mul_le_mul_right p hp5]

lemma Qtilde_GV_outer_raw (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) : GV p (Qtilde n) (outerRawBound p n + normVal p n) := by
  exact Qtilde_GV_prime' p (by omega) (by omega) n (outer_prime_square hp5 hnp)

lemma Qtilde_GV_outer_w1 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) (hlo : 3*p ≤ 4*n) : GV p (Qtilde n) (3*(n:ℚ) - p + 2) := by
  have h := Qtilde_GV_outer_raw p hp5 hnp
  have hL : (4*n)/p = 3 := div_eq_of_bounds (by omega) (by omega)
  rw [outerRawBound_w1 hnp hlo, normVal_outer_low hnp (by omega) hL] at h
  convert h using 1 <;> ring

lemma Qtilde_GV_outer_w2 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) (hlo : 4*n < 3*p) (hhi : 2*p ≤ 3*n) : GV p (Qtilde n) (5*(p:ℚ) - 7*n + 1) := by
  have h := Qtilde_GV_outer_raw p hp5 hnp
  have hL : (4*n)/p = 2 := div_eq_of_bounds (by omega) (by omega)
  rw [outerRawBound_w2 hnp hlo hhi, normVal_outer_low hnp (by omega) hL] at h
  convert h using 1 <;> ring

lemma Qtilde_GV_outer_w3 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) (hlo : 3*n < 2*p) (hhi : p ≤ 2*n) : GV p (Qtilde n) ((p:ℚ) - n + 1) := by
  have h := Qtilde_GV_outer_raw p hp5 hnp
  have hL : (4*n)/p = 2 := div_eq_of_bounds (by omega) (by omega)
  rw [outerRawBound_w3 hnp hlo hhi, normVal_outer_low hnp (by omega) hL] at h
  convert h using 1 <;> ring

lemma Qtilde_GV_outer_w4 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) (hlo : 2*n < p) (hhi : p ≤ 3*n) : GV p (Qtilde n) (3*(p:ℚ) - 7*n - 1) := by
  have h := Qtilde_GV_outer_raw p hp5 hnp
  have hL : (4*n)/p = 1 := div_eq_of_bounds (by omega) (by omega)
  rw [outerRawBound_w4 hnp hlo hhi, normVal_outer_high hnp (by omega) hL] at h
  convert h using 1 <;> ring

lemma Qtilde_GV_outer_w5 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) (hlo : 3*n < p) (hhi : p ≤ 4*n) : GV p (Qtilde n) (2*(n:ℚ) - 1) := by
  have h := Qtilde_GV_outer_raw p hp5 hnp
  have hL : (4*n)/p = 1 := div_eq_of_bounds (by omega) (by omega)
  rw [outerRawBound_w5 hnp hlo hhi, normVal_outer_high hnp (by omega) hL] at h
  convert h using 1 <;> ring

def outerPrimeBound (p n : ℕ) : ℚ :=
  if 3*p ≤ 4*n then 3*(n:ℚ)-p+2
  else if 2*p ≤ 3*n then 5*(p:ℚ)-7*n+1
  else if p ≤ 2*n then (p:ℚ)-n+1
  else if p ≤ 3*n then 3*(p:ℚ)-7*n-1
  else 2*(n:ℚ)-1

theorem Qtilde_GV_outer (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) (hpn : p ≤ 4*n) :
    GV p (Qtilde n) (outerPrimeBound p n) := by
  unfold outerPrimeBound
  split_ifs with h1 h2 h3 h4
  · exact Qtilde_GV_outer_w1 p hp5 hnp h1
  · exact Qtilde_GV_outer_w2 p hp5 hnp (by omega) h2
  · exact Qtilde_GV_outer_w3 p hp5 hnp (by omega) h3
  · exact Qtilde_GV_outer_w4 p hp5 hnp (by omega) h4
  · exact Qtilde_GV_outer_w5 p hp5 hnp (by omega) hpn

theorem Qtilde_GV_outer_or_large (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {n : ℕ}
    (hnp : n < p) :
    GV p (Qtilde n) (if p ≤ 4*n then outerPrimeBound p n else 0) := by
  split_ifs with hpn
  · exact Qtilde_GV_outer p hp5 hnp hpn
  · exact Qtilde_GV_large p (by omega) (by omega) (by omega)

theorem Qtilde_GV_outer_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    GV p (Qtilde 0) 0 := by
  exact Qtilde_GV_large p (by omega) (by omega) (by omega)

end
end Li2

end
