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

def γj (n j : ℕ) : ℚ[X] :=
  C (rscale n (4*n) j * ((j:ℚ) * (-2:ℚ)^j)) * (X - C (tau j))

lemma γj_eq_zero {n j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : γj n j = 0 := by
  simp [γj, rscale, D_eval_neg_of_le h1 h2]

lemma nat_VG_dvd (p : ℕ) [hp : Fact p.Prime] (j : ℕ) (hj : 0 < j) :
    VG p (j:ℚ) (if p ∣ j then 1 else 0) := by
  split_ifs with h
  · right
    rw [padicValRat.of_nat]
    exact_mod_cast one_le_padicValNat_of_dvd (by omega) h
  · exact VG.natCast j

theorem γj_GV (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {n j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ 4*n)
    (hK : 4*n < p^2) : GV p (γj n j) (wv n p j) := by
  by_cases hjn : j ≤ n
  · rw [γj_eq_zero hj1 hjn]; exact GV.zero _
  · push_neg at hjn
    have hr : VG p (rscale n (4*n) j)
        (2 * ((j-1)/p : ℕ) - 3 * ((j-1-n)/p : ℕ) - ((4*n-j)/p : ℕ) : ℚ) :=
      VG.of_eq _ fun _ => by rw [rscale_val p hjn hjK hK]; push_cast; exact le_rfl
    have hjv := nat_VG_dvd p j (by omega)
    have h2 := negTwo_pow_unit p hp2 j
    have ht : GV p (X - C (tau j)) (-(if p ≤ j then 2 else 0)) := by
      split_ifs with hpj
      · exact (GV.X.mono (by norm_num)).sub (GV.C (tau_VG_small p hp2 hjK hK))
      · have h0 : VG p (tau j) 0 := by
          have := tau_VG_of_ne_two p hp2 (N := j) le_rfl
          rwa [Nat.log_of_lt (by omega), Nat.cast_zero, mul_zero] at this
        simpa using GV.X.sub (GV.C h0)
    have := (GV.C (hr.mul (hjv.mul h2))).mul ht
    unfold wv
    rw [if_neg (by omega)]
    refine this.mono (le_of_eq ?_)
    ring

/-! ## The raw determinant as W + rank-one sum -/

lemma hankel_entry (n a b : ℕ) :
    numeratorFunctional (4*n) ((D n)^3 * X^(a+b)) =
      C (polynomialMoment (polynomialPart n (a+b))) +
      ∑ j ∈ Finset.Icc 1 (4*n), γj n j * C ((-(j:ℚ))^a * (-(j:ℚ))^b) := by
  unfold numeratorFunctional
  have hq : (D n)^3 * X^(a+b) /ₘ D (4*n) = polynomialPart n (a+b) := by
    rw [polynomialPart, numerator, mul_comm]
  rw [hq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_mul, eval_pow, eval_pow, eval_X]
  unfold γj rscale eraseProd
  rw [show (D n).eval (-(j:ℚ)) ^ 3 * (-(j:ℚ))^(a+b) / ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))
      = (D n).eval (-(j:ℚ)) ^ 3 / (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, ((l:ℚ)-(j:ℚ))) *
        ((-(j:ℚ))^a * (-(j:ℚ))^b) by rw [pow_add]; ring]
  simp only [map_mul, map_pow, map_inv₀, map_neg, map_div₀]
  ring

theorem raw_Q_GV (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n : ℕ)
    (hK : 4*n < p^2) :
    GV p (Q n) (∑ c : Fin p, ∑ k ∈ Finset.range (Ccl p (4*n) c),
      min (wv n p (jn p (4*n) c k) + 2 * k) 0) := by
  have hp0 : 0 < p := hp.out.pos
  have hQ : Q n = (Matrix.of fun a b : Fin (2*n) =>
      C (polynomialMoment (polynomialPart n (a+b))) +
      ∑ c : Fin p, ∑ t ∈ Finset.range (Ccl p (4*n) c),
        γj n (jn p (4*n) c t) *
          C ((-(jn p (4*n) c t : ℚ))^(a:ℕ) * (-(jn p (4*n) c t : ℚ))^(b:ℕ))).det := by
    rw [Q, ← hankelFor_original]
    congr 1
    ext a b
    rw [hankelFor, hankel_entry,
      regroup p (4*n) hp0, ← Fin.sum_univ_eq_sum_range
        (fun c => ∑ t ∈ Finset.range (Ccl p (4*n) c), γj n (jn p (4*n) c t) *
          C ((-(jn p (4*n) c t : ℚ))^(a:ℕ) * (-(jn p (4*n) c t : ℚ))^(b:ℕ))) p]
    rfl
  rw [hQ]
  apply rank_one_GV (fun c : Fin p => Ccl p (4*n) c) (fun c t => -(jn p (4*n) c t : ℚ))
    (fun c t => γj n (jn p (4*n) c t)) p (fun c t => wv n p (jn p (4*n) c t))
  · intro a b
    exact GV.C (polynomialPartMoment_VG p hp3 n _)
  · intro c t
    exact (VG.natCast _).neg
  · intro c s t hs ht hst
    have hpv : VG p (p:ℚ) 1 := by
      right; rw [padicValRat.self hp.out.one_lt]; norm_num
    have key : ∀ u v : ℕ, u ≤ v → v < Ccl p (4*n) c →
        (jn p (4*n) c u : ℚ) = jn p (4*n) c v + (p:ℚ) * ((v - u : ℕ) : ℚ) := by
      intro u v huv hv
      have hN : jn p (4*n) c u = jn p (4*n) c v + p * (v - u) := by
        unfold jn
        rw [show Ccl p (4*n) c - 1 - u = (Ccl p (4*n) c - 1 - v) + (v - u) by omega, Nat.mul_add]
        ring
      rw [hN]; push_cast; ring
    rcases lt_or_gt_of_ne hst with h | h
    · rw [key s t h.le ht]
      have := hpv.mul (VG.natCast (p := p) (t - s))
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using this
    · rw [key t s h.le hs]
      have := (hpv.mul (VG.natCast (p := p) (s - t))).neg
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using this
  · intro c t ht
    exact γj_GV p hp2 (by unfold jn; omega) (jn_le p (4*n) hp0 ht) hK
  · intro c s t hst ht
    by_cases hjt : jn p (4*n) c t ≤ n
    · have := wv_le_big (n := n) (p := p) (jn_le p (4*n) hp0 (lt_of_le_of_lt hst ht))
      simp only [wv, if_pos hjt]
      exact this
    · push_neg at hjt
      have e : jn p (4*n) c s = jn p (4*n) c t + p * (t - s) := by
        unfold jn
        rw [show Ccl p (4*n) c - 1 - s = (Ccl p (4*n) c - 1 - t) + (t - s) by omega, Nat.mul_add]
        ring
      rw [e]
      exact wv_step hp0 hjt (e ▸ jn_le p (4*n) hp0 (lt_of_le_of_lt hst ht))

end
end Li2

end
