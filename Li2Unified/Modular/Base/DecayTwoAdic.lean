module
public import Li2Unified.Modular.Base.DecayJetBounds
public import Li2Unified.Modular.Base.DecayExpand
public import Li2Unified.Modular.Base.DecayThreeAdic

set_option backward.privateInPublic true

@[expose] public section

/-! the 2-adic bound for the SAME Qtilde n.
binomGram n = W * Cmat with slots: one m=0 slot, three slots (s=0,1,2) at every node
m=n+1..4n, and 2n tail slots. The m<=n nodes vanish identically. Slot weights are
0, m-2L, 4n+1-2L with L = log_2(7n-2); injective slot choices are ranked by
theta. Result: v_2(Qtilde n) >= A2 n - 4nL, A2 n = sum_{k<2n-1}(n+1+floor(k/3)). -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section

abbrev Slot (n : ℕ) := Fin 1 ⊕ ((Fin (3*n) × Fin 3) ⊕ Fin (2*n))

def nodeOf (n : ℕ) (μ : Fin (3*n)) : ℕ := n + 1 + μ.val

def Wm (n : ℕ) : Matrix (Fin (2*n)) (Slot n) ℚ[X] := fun a i =>
  match i with
  | Sum.inl _ => C ((shiftBinom n).eval 0 ^ 3 * (binomPoly a).eval 0)
  | Sum.inr (Sum.inl (μ, s)) => C (djet (binomPoly a) (nodeOf n μ) s.val)
  | Sum.inr (Sum.inr b') => C (tailC (4*n) (gramNum n a b'))

def Cmat (n : ℕ) : Matrix (Slot n) (Fin (2*n)) ℚ[X] := fun i b =>
  match i with
  | Sum.inl _ => C (-(binomPoly b).eval 0)
  | Sum.inr (Sum.inl (μ, s)) => C ((-2:ℚ)^(nodeOf n μ)) *
      ∑ s' ∈ Finset.range 3, kap n (nodeOf n μ) s.val s' *
        C (djet (binomPoly b) (nodeOf n μ) s')
  | Sum.inr (Sum.inr b') => if b' = b then 1 else 0

lemma gramNum_eval_zero (n a b : ℕ) :
    (gramNum n a b).eval 0 / ((4*n).factorial : ℚ) =
      (shiftBinom n).eval 0 ^ 3 * (binomPoly a).eval 0 * (binomPoly b).eval 0 := by
  rw [gramNum_eq, eval_mul, eval_C, pab]
  have : ((4*n).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  simp [eval_mul, eval_pow]

lemma node_block (n : ℕ) (μ : Fin (3*n)) (a b : Fin (2*n)) :
    ∑ s : Fin 3, Wm n a (Sum.inr (Sum.inl (μ, s))) * Cmat n (Sum.inr (Sum.inl (μ, s))) b =
      C ((-2:ℚ)^(nodeOf n μ)) * localB (4*n) (nodeOf n μ) (gramNum n a b) := by
  rw [localB_gram]
  simp only [Wm, Cmat, Fin.sum_univ_three, Finset.sum_range_succ, Finset.sum_range_zero,
    Fin.val_zero, Fin.val_one, Fin.val_two, zero_add]
  ring

lemma sum_nodes (n : ℕ) (g : ℕ → ℚ[X]) (hg : ∀ m, 1 ≤ m → m ≤ n → g m = 0) :
    ∑ m ∈ Finset.Icc 1 (4*n), g m = ∑ μ : Fin (3*n), g (nodeOf n μ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ n+1) (by omega : n+1 ≤ 4*n+1),
    Finset.sum_eq_zero (s := Finset.Ico 1 (n+1)) (fun m hm => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hm; exact hg m h1 (by omega)), zero_add,
    Finset.sum_Ico_eq_sum_range, show 4*n+1-(n+1) = 3*n by omega,
    ← Fin.sum_univ_eq_sum_range (fun k => g (n+1+k))]
  rfl

theorem binomGram_eq_mul (n : ℕ) : binomGram n = Wm n * Cmat n := by
  ext a b
  rw [binomGram_apply, reflected_rep, Matrix.mul_apply, Fintype.sum_sum_type,
    Fintype.sum_sum_type, Fin.sum_univ_one, Fintype.sum_prod_type]
  simp only [node_block]
  rw [sum_nodes n (fun m => C ((-2:ℚ)^m) * localB (4*n) m (gramNum n a b))
    (fun m h1 h2 => by simp [localB_gram_low h1 h2])]
  have htail : ∑ b' : Fin (2*n), Wm n a (Sum.inr (Sum.inr b')) * Cmat n (Sum.inr (Sum.inr b')) b =
      C (tailC (4*n) (gramNum n a b)) := by
    simp [Wm, Cmat]
  rw [htail, gramNum_eval_zero]
  simp only [Wm, Cmat, map_neg, map_mul]
  ring

/-! ## Valuations at 2 -/

lemma padicValRat_two_neg_two : padicValRat 2 (-2 : ℚ) = 1 := by
  rw [padicValRat.neg]
  have := padicValRat.self (p := 2) (by norm_num)
  simpa using this

lemma negTwo_pow_VG (m : ℕ) : VG 2 ((-2:ℚ)^m) (m:ℚ) := by
  right
  rw [padicValRat.pow (by norm_num), padicValRat_two_neg_two]
  simp

section Bounds
variable {n : ℕ} (hn : 1 ≤ n)
include hn

local notation "L" => ((Nat.log 2 (7*n-2) : ℕ) : ℚ)

lemma L_nonneg : (0:ℚ) ≤ L := Nat.cast_nonneg _

lemma log_le_L {d : ℕ} (hd : d ≤ 7*n-2) : ((Nat.log 2 d : ℕ) : ℚ) ≤ L := by
  exact_mod_cast Nat.log_mono_right hd

lemma bhat_GV {m : ℕ} (hm : m ∈ Finset.Icc 1 (4*n)) {t : ℕ} (ht : t ≤ 2) :
    GV 2 (bhat (4*n) m t) (-(2 - (t:ℚ)) * L) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := L_nonneg hn
  have e1 : VG 2 (eps (4*n) m 1) (-(1:ℚ) * L) := by
    simpa using eps_VG 2 (N := 7*n-2) hm (by omega) (k := 1) (by norm_num)
  have e2 : VG 2 (eps (4*n) m 2) (-(2:ℚ) * L) := by
    simpa using eps_VG 2 (N := 7*n-2) hm (by omega) (k := 2) le_rfl
  have hC : VG 2 (Cst (4*n)) (-2 * L) := Cst_VG 2 (by omega)
  have hm' := VG.natCast (p := 2) m
  have t1 : VG 2 (eps (4*n) m 1) (-2 * L) := e1.mono (by linarith)
  have t2 : VG 2 (eps (4*n) m 1 ^ 2) (-2 * L) := by
    have := e1.pow 2
    refine this.mono (le_of_eq ?_)
    push_cast; ring
  have t3 : VG 2 ((m:ℚ) * (eps (4*n) m 1 ^ 2 - eps (4*n) m 2)) (-2 * L) := by
    have := hm'.mul (t2.sub e2)
    simpa using this
  have t4 : VG 2 ((m:ℚ) * Cst (4*n)) (-2 * L) := by
    have := hm'.mul hC
    simpa using this
  have tX : GV 2 (C (m:ℚ) * X) (-2 * L) :=
    (GV.mul (GV.C hm') GV.X).mono (by linarith)
  interval_cases t
  · have g : GV 2 (bhat (4*n) m 0) (-2 * L) := by
      simp only [bhat]
      exact GV.add (GV.C ((t1.add t3).add t4)) tX
    convert g using 2
    push_cast; ring
  · have g : GV 2 (bhat (4*n) m 1) (-1 * L) := by
      simp only [bhat]
      exact GV.C (((VG.one (p := 2)).neg.mono (by linarith)).sub (by simpa using hm'.mul e1))
    convert g using 2
    push_cast; ring
  · have g : GV 2 (bhat (4*n) m 2) 0 := by
      simp only [bhat]
      exact GV.C hm'
    convert g using 2
    push_cast; ring

lemma kap_GV {m : ℕ} (hm : m ∈ Finset.Icc 1 (4*n)) (s s' : ℕ) :
    GV 2 (kap n m s s') (((s:ℚ) + s' - 2) * L) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hm
  have hL := L_nonneg hn
  have hsig : JGV 2 ((shiftBinom n ^ 3).comp (X - C (m:ℚ))) L := by
    rw [pow_comp]
    exact (shiftBinom_JGV 2 n m (log_le_L hn (by omega))).pow 3
  unfold kap
  apply GV.sum
  intro i hi
  have hi2 : i ≤ 2 := by simp at hi; omega
  split_ifs with hle
  · have hscale := residueScale_VG 2 (K := 4*n) h1 h2
    have hc := GV.C (hscale.mul (hsig i hi2))
    refine (hc.mul (bhat_GV hn hm (t := i+s+s') hle)).mono ?_
    push_cast
    nlinarith
  · exact GV.zero _

lemma tailC_VG (a b : ℕ) (ha : a < 2*n) (hb : b < 2*n) :
    VG 2 (tailC (4*n) (gramNum n a b)) ((4*n+1 : ℕ) - 2 * L) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := L_nonneg hn
  unfold tailC
  apply VG.sub
  · -- polynomial tail
    set G := gpart (4*n) (gramNum n a b)
    have hGv : ∀ x : ℤ, VG 2 (G.eval (x:ℚ)) (-2 * L) := by
      intro x
      rw [gpart_eval]
      have hq := gramQuot_eval_VG 2 n a b x
      have hq' := derivative_eval_VG 2 (gramQuot_natDegree_le n a b) _ (gramQuot_eval_VG 2 n a b) x
      have l1 := log_le_L hn (d := 3*n+a+b) (by omega)
      have l2 := log_le_L hn (d := 3*n+a+b-4*n) (by omega)
      refine (hq.mono (by linarith)).add (((VG.intCast (p := 2) x).mul hq').mono ?_)
      linarith
    have hR := Gm_VG_of_ne_three 2 (by decide) (le_refl ((G.comp (X - C ((4*n+1 : ℕ):ℚ))).natDegree))
      (-2 * L) (fun i _ => by
        have := hGv ((i:ℤ) - ((4*n+1 : ℕ) : ℤ))
        simp only [eval_comp, eval_sub, eval_X, eval_C]
        push_cast at this ⊢
        exact this)
    refine ((negTwo_pow_VG (4*n+1)).mul hR).mono ?_
    push_cast
    linarith
  · apply VG.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres : VG 2 (dres (4*n) (gramNum n a b) j) 0 := gramRes_VG 2 n a b hj1 hj2
    have hin : VG 2 (∑ m ∈ Finset.Ico (4*n+1) (j+4*n+1), poleNode j m)
        (((4*n+1 : ℕ) : ℚ) - 2 * L) := by
      apply VG.sum
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
      have hv := poleNode_VG 2 (j := j) (m := m) (N := 7*n-2) (by omega) ⟨by omega, by omega⟩
      rw [padicValRat_two_neg_two] at hv
      refine hv.mono ?_
      have : ((4*n+1 : ℕ) : ℚ) ≤ m := by exact_mod_cast hm1
      push_cast at this ⊢
      linarith
    exact (hres.mul hin).mono (by simp)

end Bounds

/-- Column weights of W and row weights of Cmat. -/
def ωw (n : ℕ) : Slot n → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (_, s)) => -(s.val:ℚ) * ((Nat.log 2 (7*n-2) : ℕ) : ℚ)
  | Sum.inr (Sum.inr _) => ((4*n+1 : ℕ) : ℚ) - 2 * ((Nat.log 2 (7*n-2) : ℕ) : ℚ)

def κw (n : ℕ) : Slot n → ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (μ, s)) => (nodeOf n μ : ℚ) + ((s.val:ℚ) - 2) * ((Nat.log 2 (7*n-2) : ℕ) : ℚ)
  | Sum.inr (Sum.inr _) => 0

/-- The slot ranking. -/
def slotRank (n : ℕ) : Slot n → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (μ, s)) => 1 + 3 * μ.val + s.val
  | Sum.inr (Sum.inr b') => 1 + 9*n + b'.val

lemma slotRank_injective (n : ℕ) : Function.Injective (slotRank n) := by
  intro x y hxy
  rcases x with x | ⟨μ, s⟩ | b <;> rcases y with y | ⟨ν, t⟩ | c <;>
    simp only [slotRank] at hxy
  · rw [Subsingleton.elim x y]
  · omega
  · omega
  · omega
  · have := μ.isLt; have := s.isLt; have := t.isLt
    have h1 : μ.val = ν.val := by omega
    have h2 : s.val = t.val := by omega
    rw [Fin.ext h1, Fin.ext h2]
  · have := μ.isLt; have := s.isLt; omega
  · omega
  · have := ν.isLt; have := t.isLt; omega
  · rw [Fin.ext (by omega : b.val = c.val)]

def θw (n : ℕ) (i : ℕ) : ℚ :=
  (if i = 0 then 0 else ((min (n + 1 + (i-1)/3) (4*n+1) : ℕ) : ℚ)) -
    2 * ((Nat.log 2 (7*n-2) : ℕ) : ℚ)

lemma θw_mono (n : ℕ) : Monotone (θw n) := by
  intro i j hij
  unfold θw
  split_ifs with hi hj hj
  · exact le_rfl
  · have := Nat.cast_nonneg (α := ℚ) (min (n + 1 + (j-1)/3) (4*n+1))
    linarith
  · omega
  · have h1 : min (n + 1 + (i-1)/3) (4*n+1) ≤ min (n + 1 + (j-1)/3) (4*n+1) :=
      min_le_min (by have := Nat.div_le_div_right (c := 3) (by omega : i - 1 ≤ j - 1); omega) le_rfl
    have h2 : ((min (n + 1 + (i-1)/3) (4*n+1) : ℕ) : ℚ) ≤ ((min (n + 1 + (j-1)/3) (4*n+1) : ℕ) : ℚ) := by
      exact_mod_cast h1
    linarith

section Bounds2
variable {n : ℕ} (hn : 1 ≤ n)
include hn

local notation "L" => ((Nat.log 2 (7*n-2) : ℕ) : ℚ)

lemma Wm_GV (a : Fin (2*n)) (i : Slot n) : GV 2 (Wm n a i) (ωw n i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases i with _ | ⟨μ, s⟩ | b'
  · apply GV.C
    have h1 := shiftBinom_eval_int 2 n 0
    have h2 := binomPoly_eval_int_VG 2 a 0
    simp only [Int.cast_zero] at h1 h2
    simpa [ωw] using (h1.pow 3).mul h2
  · apply GV.C
    have hj := binom_JGV 2 a (nodeOf n μ) (log_le_L hn (d := a) (by have := a.isLt; omega))
    simpa [ωw] using hj s.val (by omega)
  · simpa [ωw] using GV.C (tailC_VG hn a b' a.isLt b'.isLt)

lemma Cmat_GV (i : Slot n) (b : Fin (2*n)) : GV 2 (Cmat n i b) (κw n i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := L_nonneg hn
  rcases i with _ | ⟨μ, s⟩ | b'
  · apply GV.C
    have h2 := binomPoly_eval_int_VG 2 b 0
    simp only [Int.cast_zero] at h2
    simpa [κw] using h2.neg
  · have hm : nodeOf n μ ∈ Finset.Icc 1 (4*n) := by
      simp only [nodeOf, Finset.mem_Icc]; have := μ.isLt; omega
    have hsum : GV 2 (∑ s' ∈ Finset.range 3, kap n (nodeOf n μ) s.val s' *
        C (djet (binomPoly b) (nodeOf n μ) s')) (((s.val:ℚ) - 2) * L) := by
      apply GV.sum
      intro s' hs'
      have hs'2 : s' ≤ 2 := by simp at hs'; omega
      have hj := binom_JGV 2 b (nodeOf n μ) (log_le_L hn (d := b) (by have := b.isLt; omega))
      refine ((kap_GV hn hm s.val s').mul (GV.C (hj s' hs'2))).mono (le_of_eq ?_)
      ring
    exact (GV.mul (GV.C (negTwo_pow_VG _)) hsum).mono (le_of_eq (by simp [κw]))
  · simp only [Cmat, κw]
    split_ifs
    · exact GV.C VG.one
    · exact GV.zero _

lemma θw_le (x : Slot n) : θw n (slotRank n x) ≤ ωw n x + κw n x := by
  have hL := L_nonneg hn
  rcases x with _ | ⟨μ, s⟩ | b'
  · simp [θw, slotRank, ωw, κw]
  · simp only [θw, slotRank, ωw, κw, nodeOf]
    rw [if_neg (by omega)]
    have hdiv : (1 + 3 * μ.val + s.val - 1) / 3 = μ.val := by have := s.isLt; omega
    rw [hdiv]
    have h1 : ((min (n + 1 + μ.val) (4*n+1) : ℕ) : ℚ) ≤ ((n + 1 + μ.val : ℕ) : ℚ) := by
      exact_mod_cast min_le_left _ _
    push_cast at h1 ⊢
    nlinarith
  · simp only [θw, slotRank, ωw, κw]
    rw [if_neg (by omega)]
    have h1 : ((min (n + 1 + (1 + 9*n + b'.val - 1)/3) (4*n+1) : ℕ) : ℚ) ≤ ((4*n+1 : ℕ) : ℚ) := by
      exact_mod_cast min_le_right _ _
    linarith

/-- The 2-adic bound on the literal Qtilde n, as a sum of ranked slot weights. -/
theorem Qtilde_GV_two_slots : GV 2 (Qtilde n) (∑ i ∈ Finset.range (2*n), θw n i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Qtilde_eq_binomGram_det, binomGram_eq_mul]
  apply det_mul_GV 2 (Wm n) (Cmat n) (ωw n) (κw n) (Wm_GV hn) (Cmat_GV hn)
  intro f hf
  calc ∑ i ∈ Finset.range (2*n), θw n i
      ≤ ∑ b, θw n (slotRank n (f b)) :=
        sum_range_le_of_injective (θw n) (θw_mono n) (fun b => slotRank n (f b))
          ((slotRank_injective n).comp hf)
    _ ≤ ∑ b, (ωw n (f b) + κw n (f b)) := Finset.sum_le_sum fun b _ => θw_le hn (f b)

end Bounds2

def A2 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2*n-1), (n + 1 + k/3)

theorem θw_sum {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (2*n), θw n i =
      (A2 n : ℚ) - 4 * (n:ℚ) * ((Nat.log 2 (7*n-2) : ℕ) : ℚ) := by
  have h0 : θw n 0 = -2 * ((Nat.log 2 (7*n-2) : ℕ) : ℚ) := by simp [θw]
  have hterm : ∀ i ∈ Finset.range (2*n-1), θw n (i+1) =
      ((n + 1 + i/3 : ℕ) : ℚ) - 2 * ((Nat.log 2 (7*n-2) : ℕ) : ℚ) := by
    intro i hi
    have hi' : i < 2*n-1 := Finset.mem_range.mp hi
    simp only [θw, if_neg (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
    rw [min_eq_left (by omega)]
  rw [show 2*n = (2*n-1) + 1 by omega, Finset.sum_range_succ', h0, Finset.sum_congr rfl hterm,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, A2, Nat.cast_sum]
  rw [show ((2*n-1 : ℕ) : ℚ) = 2*(n:ℚ) - 1 by rw [Nat.cast_sub (by omega)]; push_cast; ring]
  ring

/-- Every coefficient of Qtilde n has v_2 >= A2 n - 4n log_2(7n-2), n >= 1. -/
theorem Qtilde_GV_two {n : ℕ} (hn : 1 ≤ n) :
    GV 2 (Qtilde n) ((A2 n : ℚ) - 4 * (n:ℚ) * ((Nat.log 2 (7*n-2) : ℕ) : ℚ)) := by
  rw [← θw_sum hn]
  exact Qtilde_GV_two_slots hn

/-- A2 n >= (8n^2 - 4n)/3: the 2-adic saving is 8n^2/3 - O(n log n). -/
theorem A2_lower (n : ℕ) (hn : 1 ≤ n) : 8 * n^2 ≤ 3 * A2 n + 4 * n := by
  have hk : ∀ k ∈ Finset.range (2*n-1), 3*n + 1 + k ≤ 3 * (n + 1 + k/3) := fun k _ => by omega
  have hs := Finset.sum_le_sum hk
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at hs
  have hid := Finset.sum_range_id_mul_two (2*n-1)
  unfold A2
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2*(1+t)-1 = 2*t+1 by omega] at hs hid ⊢
  rw [show 2*t+1-1 = 2*t by omega] at hid
  nlinarith [hs, hid]

end
end Li2

end
