module
public import Li2Unified.Modular.Positive.Packed.P046
public import Li2Unified.Modular.Positive.Packed.P036
public import Li2Unified.Modular.Base.PrimeTwoThreeSum
public import Li2Unified.Modular.Positive.Packed.P001
public import Li2Unified.Modular.Base.ParameterShift
public import Li2Unified.Modular.Base.DecayLocal
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.DecayTwoAdic

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Filter Topology

namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf

/-- The primitive scale inherits the actual positive-half good-prime fallback at three. -/
theorem posHalf_dtilde_three_lower (n : ℕ) (hn : 1 ≤ n)
    (hne : Instances.PosHalf.Qtilde n ≠ 0) :
    (-(4 * n * Nat.log 3 (7*n-2) : ℕ) : ℚ) ≤
      (-padicValRat 3 (dtilde lambda n) : ℚ) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨k, hk0, hkval, _⟩ :=
    Qtilde_coeff_valuation_minimum lambda 3
      (by simpa only [Instances.PosHalf.Qtilde] using! hne)
  have hcoeff := (posHalf_three_adic_good_fallback n hn) k
  change Li2.VG 3 ((ParameterFamily.Qtilde lambda n).coeff k) _ at hcoeff
  rcases hcoeff with hzero | hbound
  · exact (hk0 hzero).elim
  · rw [hkval] at hbound
    simpa only using! hbound

/-- The exact Stage0 three-adic statement, expressed before its contentTerm wrapper. -/
theorem posHalf_three_adic_content_raw :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      Instances.PosHalf.Qtilde n ≠ 0 →
        -ε * (n:ℝ)^2 ≤
          ((-padicValRat 3 (dtilde lambda n) : ℤ) : ℝ) * Real.log 3 := by
  intro ε hε
  have hlim : Tendsto
      (fun n : ℕ =>
        (-(4*(n:ℝ)*(Nat.log 3 (7*n-2):ℝ)) * Real.log 3) / (n:ℝ)^2)
      atTop (𝓝 (0:ℝ)) := by
    convert (Li2.PrimeSums.natLog_error_square_tendsto_zero 3).neg.mul_const
      (Real.log 3) using 1 <;> ext n <;> ring
  have hnear : ∀ᶠ n : ℕ in atTop,
      -ε < (-(4*(n:ℝ)*(Nat.log 3 (7*n-2):ℝ)) * Real.log 3) / (n:ℝ)^2 :=
    hlim.eventually (isOpen_Ioi.mem_nhds (show -ε < (0:ℝ) by linarith))
  filter_upwards [hnear, eventually_ge_atTop (1:ℕ)] with n hnear hn
  intro hne
  have hv := posHalf_dtilde_three_lower n hn hne
  have hvR : -(4*(n:ℝ)*(Nat.log 3 (7*n-2):ℝ)) ≤
      ((-padicValRat 3 (dtilde lambda n) : ℤ) : ℝ) := by
    exact_mod_cast hv
  have hsq : 0 < (n:ℝ)^2 := by
    have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hlog : 0 ≤ Real.log 3 := le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 3))
  calc
    -ε*(n:ℝ)^2 ≤
        ((-(4*(n:ℝ)*(Nat.log 3 (7*n-2):ℝ)) * Real.log 3) /
          (n:ℝ)^2) * (n:ℝ)^2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hnear) hsq.le
    _ = -(4*(n:ℝ)*(Nat.log 3 (7*n-2):ℝ)) * Real.log 3 := by
      field_simp [hsq.ne']
    _ ≤ ((-padicValRat 3 (dtilde lambda n) : ℤ) : ℝ) * Real.log 3 :=
      mul_le_mul_of_nonneg_right hvR hlog

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.posHalf_dtilde_three_lower
#print axioms Li2Unified.Proofs.Arithmetic.posHalf_three_adic_content_raw

end

section
open Polynomial
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- One backward step for the parameter functional in the original family. -/
lemma parameterG_back_one (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (R : ℚ[X]) :
    Li2.parameterG lam R = lam⁻¹ * Li2.parameterG lam (R.comp (X-1)) - R.eval 0 := by
  have h := Li2.parameterG_shift_one lam h1 (R.comp (X-1))
  have hc : (R.comp (X-1)).comp (X+1) = R := by
    rw [comp_assoc, sub_comp, X_comp, one_comp, add_sub_cancel_right, comp_X]
  rw [hc] at h
  have he : (R.comp (X-1)).eval 1 = R.eval 0 := by simp [eval_comp]
  rw [he] at h
  apply (mul_left_cancel₀ h0)
  calc
    lam * Li2.parameterG lam R = Li2.parameterG lam (R.comp (X-1)) - lam * R.eval 0 := h
    _ = lam * (lam⁻¹ * Li2.parameterG lam (R.comp (X-1)) - R.eval 0) := by
      field_simp [h0]

/-- Finite reflection for every nonzero rational parameter other than one. -/
theorem parameterG_back (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (R : ℚ[X]) (M : ℕ) :
    Li2.parameterG lam R =
      -(∑ m ∈ Finset.range M, (lam⁻¹)^m * R.eval (-(m:ℚ))) +
        (lam⁻¹)^M * Li2.parameterG lam (R.comp (X-C (M:ℚ))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, parameterG_back_one lam h0 h1 (R.comp (X-C (M:ℚ)))]
    have hc : (R.comp (X-C (M:ℚ))).comp (X-1) =
        R.comp (X-C ((M+1:ℕ):ℚ)) := by
      rw [comp_assoc, sub_comp, X_comp, C_comp]
      congr 1
      push_cast
      rw [map_add, map_one]
      ring
    have he : (R.comp (X-C (M:ℚ))).eval 0 = R.eval (-(M:ℚ)) := by
      simp [eval_comp]
    rw [hc, he, Finset.sum_range_succ, pow_succ]
    ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameterG_back

end

section
open Polynomial
open Li2
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- Reflected node for the actual parameter family; at positive half the weight is `2^m`. -/
def parameterPoleNode (lam : ℚ) (j m : ℕ) : ℚ :=
  (j:ℚ) * lam⁻¹^m / (((j:ℚ) - m))^2

def parameterCst (lam : ℚ) (K : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 K, lam⁻¹^a / ((a:ℚ))^2

lemma parameterPoleNode_self (lam : ℚ) (j : ℕ) : parameterPoleNode lam j j = 0 := by
  simp [parameterPoleNode]

/-- The original `parameterTau` turns into the nodes below the pole. -/
lemma parameterTau_node (lam : ℚ) (h0 : lam ≠ 0) (j : ℕ) :
    (j:ℚ) * lam⁻¹^j * Li2.parameterTau lam j =
      ∑ m ∈ Finset.range j, parameterPoleNode lam j m := by
  unfold Li2.parameterTau
  rw [Li2.sum_Icc_one_eq_range, Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < j := Finset.mem_range.mp hk
  unfold parameterPoleNode
  have e1 : j - 1 - k + 1 = j - k := by omega
  rw [e1]
  have e2 : lam⁻¹^j * lam^(j-k) = lam⁻¹^k := by
    calc
      lam⁻¹^j * lam^(j-k) = lam⁻¹^k * (lam⁻¹^(j-k) * lam^(j-k)) := by
        nth_rewrite 1 [show j = k + (j-k) by omega]
        rw [pow_add]
        ring
      _ = lam⁻¹^k := by
        rw [← mul_pow, inv_mul_cancel₀ h0]
        simp
  have e3 : ((j - k : ℕ) : ℚ) = (j:ℚ) - k := by rw [Nat.cast_sub hk'.le]
  rw [e3]
  calc
    (j:ℚ) * lam⁻¹^j * (lam^(j-k) / ((j:ℚ) - k)^2)
        = (j:ℚ) * (lam⁻¹^j * lam^(j-k)) / ((j:ℚ) - k)^2 := by ring
    _ = (j:ℚ) * lam⁻¹^k / ((j:ℚ) - k)^2 := by rw [e2]

/-- The extra `K` reflected nodes encode the constant shift of the pole value. -/
lemma parameterCst_node (lam : ℚ) (K j : ℕ) :
    (j:ℚ) * lam⁻¹^j * parameterCst lam K =
      ∑ m ∈ Finset.Ico (j+1) (j+K+1), parameterPoleNode lam j m := by
  unfold parameterCst
  rw [Li2.sum_Icc_one_eq_range, Finset.mul_sum, Finset.sum_Ico_eq_sum_range,
    show j + K + 1 - (j+1) = K by omega]
  apply Finset.sum_congr rfl
  intro k _
  unfold parameterPoleNode
  have e : ((j + 1 + k : ℕ) : ℚ) = (j:ℚ) + ((k:ℚ)+1) := by push_cast; ring
  rw [e, show j + 1 + k = j + (k+1) by ring, pow_add]
  have he : ((j:ℚ) - ((j:ℚ) + ((k:ℚ)+1)))^2 = (((k+1:ℕ):ℚ))^2 := by
    push_cast
    ring
  rw [he]
  ring

/-- A finite exact pole split, with no limiting or convergence assumption. -/
theorem parameterPole_split (lam : ℚ) (h0 : lam ≠ 0) (K j : ℕ) :
    (j:ℚ) * lam⁻¹^j * (Li2.parameterTau lam j + parameterCst lam K) =
      ∑ m ∈ Finset.range (j+K+1), parameterPoleNode lam j m := by
  rw [mul_add, parameterTau_node lam h0, parameterCst_node,
    Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le j) (by omega : j ≤ j+K+1),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : j < j+K+1),
    parameterPoleNode_self, zero_add]

def parameterTailC (lam : ℚ) (K : ℕ) (F : ℚ[X]) : ℚ :=
  lam⁻¹^(K+1) * Li2.parameterG lam ((Li2.gpart K F).comp (X - C ((K+1 : ℕ):ℚ))) -
    ∑ j ∈ Finset.Icc 1 K, Li2.dres K F j *
      ∑ m ∈ Finset.Ico (K+1) (j+K+1), parameterPoleNode lam j m

def parameterLocalB (lam : ℚ) (K m : ℕ) (F : ℚ[X]) : ℚ[X] :=
  C (Li2.localC K m F + (m:ℚ) * Li2.dres K F m * parameterCst lam K) +
    C ((m:ℚ) * Li2.dres K F m) * X

theorem parameterReflected_rep (lam : ℚ) (hlam : lam ≠ 0) (h1 : lam ≠ 1) (K : ℕ) (F : ℚ[X]) :
    ParameterFamily.numeratorFunctional lam K F = C (-(F.eval 0 / (K.factorial : ℚ))) +
      ∑ m ∈ Finset.Icc 1 K, C (lam⁻¹^m) * parameterLocalB lam K m F + C (parameterTailC lam K F) := by
  set r := fun j => dres K F j with hr
  set G := gpart K F with hG
  set q := F /ₘ D K with hq
  -- affine form of the left side
  have hA : ParameterFamily.numeratorFunctional lam K F =
      C (Li2.parameterU lam q - ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j * Li2.parameterTau lam j)) +
      C (∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j)) * X := by
    unfold ParameterFamily.numeratorFunctional
    have hterm : ∀ j ∈ Finset.Icc 1 K,
        C (F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 K).erase j, ((l:ℚ)-(j:ℚ))) *
          (C ((j:ℚ)*lam⁻¹^j) * (X - C (Li2.parameterTau lam j))) =
        C (r j * ((j:ℚ) * lam⁻¹^j)) * X - C (r j * ((j:ℚ) * lam⁻¹^j * Li2.parameterTau lam j)) := by
      intro j _
      simp only [hr, dres, eraseProd, map_mul]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
      ← map_sum, map_sub]
    ring
  -- affine form of the right side
  have hB : ∑ m ∈ Finset.Icc 1 K, C (lam⁻¹^m) * parameterLocalB lam K m F =
      C (∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * (localC K m F + (m:ℚ) * r m * parameterCst lam K)) +
      C (∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * ((m:ℚ) * r m)) * X := by
    have hterm : ∀ m ∈ Finset.Icc 1 K, C (lam⁻¹^m) * parameterLocalB lam K m F =
        C (lam⁻¹^m * (localC K m F + (m:ℚ) * r m * parameterCst lam K)) +
        C (lam⁻¹^m * ((m:ℚ) * r m)) * X := by
      intro m _
      simp only [parameterLocalB, hr, map_mul]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum, ← map_sum]
  rw [hA, hB]
  -- scalar identities
  have hX : ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j) =
      ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * ((m:ℚ) * r m) :=
    Finset.sum_congr rfl fun j _ => by ring
  have hPM : Li2.parameterU lam q = -(G.eval 0 +
      ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * G.eval (-(m:ℚ))) +
      lam⁻¹^(K+1) * Li2.parameterG lam (G.comp (X - C ((K+1 : ℕ):ℚ))) := by
    rw [Li2.parameterU, parameterG_back lam hlam h1 _ (K+1), range_succ_split]
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero]
    rfl
  have hloc : ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * localC K m F =
      -(∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * G.eval (-(m:ℚ))) -
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Icc 1 K, parameterPoleNode lam j m := by
    have h1 : ∀ m ∈ Finset.Icc 1 K, lam⁻¹^m * localC K m F =
        -(lam⁻¹^m * G.eval (-(m:ℚ))) - ∑ j ∈ Finset.Icc 1 K, r j * parameterPoleNode lam j m := by
      intro m hm
      rw [localC_eq hm, hG, gpart_eval, mul_sub, Finset.mul_sum]
      have hs : ∑ j ∈ Finset.Icc 1 K, lam⁻¹^m * (dres K F j * ((j:ℚ) / ((j:ℚ) - m)^2)) =
          ∑ j ∈ Finset.Icc 1 K, r j * parameterPoleNode lam j m :=
        Finset.sum_congr rfl fun j _ => by simp only [hr, parameterPoleNode]; ring
      rw [hs]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have h0 : F.eval 0 / (K.factorial : ℚ) = G.eval 0 +
      ∑ j ∈ Finset.Icc 1 K, r j * parameterPoleNode lam j 0 := by
    rw [eval_zero_rep, hG, gpart_eval]
    simp [hr, parameterPoleNode, Li2.poleNode]
  have htau : ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j * Li2.parameterTau lam j) =
      ∑ j ∈ Finset.Icc 1 K, r j * parameterPoleNode lam j 0 +
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Icc 1 K, parameterPoleNode lam j m +
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Ico (K+1) (j+K+1), parameterPoleNode lam j m -
      ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j * parameterCst lam K) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hs := parameterPole_split lam hlam K j
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : K+1 ≤ j+K+1), range_succ_split] at hs
    have : (j:ℚ) * lam⁻¹^j * Li2.parameterTau lam j = parameterPoleNode lam j 0 + ∑ m ∈ Finset.Icc 1 K, parameterPoleNode lam j m +
        ∑ m ∈ Finset.Ico (K+1) (j+K+1), parameterPoleNode lam j m - (j:ℚ) * lam⁻¹^j * parameterCst lam K := by
      linear_combination hs
    rw [this]
    ring
  have hCs : ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * ((m:ℚ) * r m * parameterCst lam K) =
      ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j * parameterCst lam K) :=
    Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * (localC K m F + (m:ℚ) * r m * parameterCst lam K) =
      ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * localC K m F +
      ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * ((m:ℚ) * r m * parameterCst lam K) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hT : parameterTailC lam K F = lam⁻¹^(K+1) * Li2.parameterG lam (G.comp (X - C ((K+1 : ℕ):ℚ))) -
      ∑ j ∈ Finset.Icc 1 K, r j * ∑ m ∈ Finset.Ico (K+1) (j+K+1), parameterPoleNode lam j m := rfl
  rw [hX, hsplit]
  have hscal : Li2.parameterU lam q - ∑ j ∈ Finset.Icc 1 K, r j * ((j:ℚ) * lam⁻¹^j * Li2.parameterTau lam j) =
      -(F.eval 0 / (K.factorial : ℚ)) +
      (∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * localC K m F +
        ∑ m ∈ Finset.Icc 1 K, lam⁻¹^m * ((m:ℚ) * r m * parameterCst lam K)) + parameterTailC lam K F := by
    rw [hPM, hloc, h0, htau, hCs, hT]
    ring
  rw [hscal, map_add, map_add, map_add, map_neg]
  ring


end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameterPole_split
#print axioms Li2Unified.Proofs.Arithmetic.parameterReflected_rep

end

section
open Polynomial Li2
open scoped BigOperators

namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- Only the constant term of the local jet changes with the parameter. -/
def parameterBhat (lam : ℚ) (K m : ℕ) : ℕ → ℚ[X]
  | 0 => C (eps K m 1 + (m:ℚ) * (eps K m 1 ^ 2 - eps K m 2) +
      (m:ℚ) * parameterCst lam K) + C (m:ℚ) * X
  | 1 => C (-1 - (m:ℚ) * eps K m 1)
  | 2 => C (m:ℚ)
  | _ => 0

theorem parameterLocalB_jets (lam : ℚ) (K m : ℕ) (F : ℚ[X]) :
    parameterLocalB lam K m F = C (1 / eraseProd K m) *
      (C (djet F m 0) * parameterBhat lam K m 0 +
        C (djet F m 1) * parameterBhat lam K m 1 +
        C (djet F m 2) * parameterBhat lam K m 2) := by
  unfold parameterLocalB localC dres
  rw [← djet_zero_eq]
  simp only [parameterBhat, div_eq_mul_inv, map_add, map_mul, map_sub,
    map_neg, map_one, map_pow, one_mul]
  ring

/-- Same three-by-three jet kernel, now with the correct parameter constant. -/
def parameterKap (lam : ℚ) (n m : ℕ) (s s' : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range 3, if i + s + s' ≤ 2 then
    C (((4*n).factorial : ℚ) / eraseProd (4*n) m *
      ((shiftBinom n ^ 3).comp (X - C (m:ℚ))).coeff i) *
      parameterBhat lam (4*n) m (i + s + s')
    else 0

theorem parameterLocalB_gram (lam : ℚ) (n m a b : ℕ) :
    parameterLocalB lam (4*n) m (gramNum n a b) =
      ∑ s ∈ Finset.range 3, ∑ s' ∈ Finset.range 3,
        C (djet (binomPoly a) m s) * parameterKap lam n m s s' *
          C (djet (binomPoly b) m s') := by
  rw [parameterLocalB_jets]
  have hg : ∀ k, djet (gramNum n a b) m k = ((4*n).factorial : ℚ) *
      (((shiftBinom n ^ 3).comp (X - C (m:ℚ)) * (binomPoly a).comp (X - C (m:ℚ))) *
        (binomPoly b).comp (X - C (m:ℚ))).coeff k := by
    intro k
    rw [gramNum_eq, djet_C_mul, pab, djet, mul_comp, mul_comp]
  simp only [hg, coeff_two_mul, coeff_one_mul, mul_coeff_zero]
  simp only [parameterKap, djet, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [div_eq_mul_inv]
  ring

theorem parameterLocalB_gram_low (lam : ℚ) {n m : ℕ}
    (h1 : 1 ≤ m) (h2 : m ≤ n) (a b : ℕ) :
    parameterLocalB lam (4*n) m (gramNum n a b) = 0 := by
  have hdvd : X - C (-(m:ℚ)) ∣ shiftBinom n :=
    dvd_iff_isRoot.mpr (shiftBinom_root h1 h2)
  obtain ⟨T, hT⟩ := hdvd
  have hS : (shiftBinom n ^ 3).comp (X - C (m:ℚ)) =
      X^3 * (T.comp (X - C (m:ℚ)))^3 := by
    rw [hT, pow_comp, mul_comp, sub_comp, X_comp, C_comp, map_neg,
      sub_neg_eq_add, sub_add_cancel]
    ring
  have hz : ∀ k ≤ 2, djet (gramNum n a b) m k = 0 := by
    intro k hk
    rw [gramNum_eq, djet_C_mul, pab, djet, mul_comp, mul_comp, hS,
      mul_assoc, mul_assoc, coeff_X_pow_mul', if_neg (by omega), mul_zero]
  rw [parameterLocalB_jets, hz 0 (by omega), hz 1 (by omega), hz 2 le_rfl]
  simp

def parameterWm (lam : ℚ) (n : ℕ) : Matrix (Fin (2*n)) (Li2.Slot n) ℚ[X] := fun a i =>
  match i with
  | Sum.inl _ => C ((shiftBinom n).eval 0 ^ 3 * (binomPoly a).eval 0)
  | Sum.inr (Sum.inl (μ, s)) => C (djet (binomPoly a) (nodeOf n μ) s.val)
  | Sum.inr (Sum.inr b') => C (parameterTailC lam (4*n) (gramNum n a b'))

def parameterCmat (lam : ℚ) (n : ℕ) : Matrix (Li2.Slot n) (Fin (2*n)) ℚ[X] := fun i b =>
  match i with
  | Sum.inl _ => C (-(binomPoly b).eval 0)
  | Sum.inr (Sum.inl (μ, s)) => C (lam⁻¹^(nodeOf n μ)) *
      ∑ s' ∈ Finset.range 3, parameterKap lam n (nodeOf n μ) s.val s' *
        C (djet (binomPoly b) (nodeOf n μ) s')
  | Sum.inr (Sum.inr b') => if b' = b then 1 else 0

lemma parameterNode_block (lam : ℚ) (n : ℕ) (μ : Fin (3*n))
    (a b : Fin (2*n)) :
    ∑ s : Fin 3, parameterWm lam n a (Sum.inr (Sum.inl (μ, s))) *
      parameterCmat lam n (Sum.inr (Sum.inl (μ, s))) b =
      C (lam⁻¹^(nodeOf n μ)) *
        parameterLocalB lam (4*n) (nodeOf n μ) (gramNum n a b) := by
  rw [parameterLocalB_gram]
  simp only [parameterWm, parameterCmat, Fin.sum_univ_three,
    Finset.sum_range_succ, Finset.sum_range_zero, Fin.val_zero,
    Fin.val_one, Fin.val_two, zero_add]
  ring

/-- Exact rank-slot factorization of the original positive-parameter Gram matrix. -/
theorem parameterBinomGram_eq_mul (lam : ℚ) (h0 : lam ≠ 0) (h1 : lam ≠ 1)
    (n : ℕ) : ParameterFamily.binomGram lam n =
      parameterWm lam n * parameterCmat lam n := by
  apply Matrix.ext
  intro a b
  change ParameterFamily.numeratorFunctional lam (4*n) (Li2.gramNum n a b) =
    (parameterWm lam n * parameterCmat lam n) a b
  rw [parameterReflected_rep lam h0 h1, Matrix.mul_apply,
    Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_one, Fintype.sum_prod_type]
  simp only [parameterNode_block]
  rw [Li2.sum_nodes n
    (fun m => C (lam⁻¹^m) * parameterLocalB lam (4*n) m (gramNum n a b))
    (fun m hm1 hm2 => by simp [parameterLocalB_gram_low lam hm1 hm2])]
  have htail : ∑ b' : Fin (2*n),
      parameterWm lam n a (Sum.inr (Sum.inr b')) *
        parameterCmat lam n (Sum.inr (Sum.inr b')) b =
        C (parameterTailC lam (4*n) (gramNum n a b)) := by
    simp [parameterWm, parameterCmat]
  rw [htail, Li2.gramNum_eval_zero]
  simp only [parameterWm, parameterCmat, map_neg, map_mul]
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.parameterBinomGram_eq_mul

end


end
