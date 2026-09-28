module
public import Li2Unified.Modular.Positive.Packed.P164
public import Li2Unified.Modular.Positive.Packed.P168

set_option backward.privateInPublic true

@[expose] public section

section
/-! Semantic bridge for the unnormalised integer-pair series used by the checker. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf

open Li2Unified.ParameterFamily

theorem qZero_toRat : qZero.toRat = 0 := by norm_num [qZero, QPair.toRat]
theorem qOne_toRat : qOne.toRat = 1 := by norm_num [qOne, QPair.toRat]
theorem qHalf_toRat : qHalf.toRat = 1 / 2 := by norm_num [qHalf, QPair.toRat]
theorem qQuarter_toRat : qQuarter.toRat = 1 / 4 := by norm_num [qQuarter, QPair.toRat]

theorem qValid_qOne : qValid qOne = true := by decide
theorem qValid_qZero : qValid qZero = true := by decide

theorem qLT_zero_num {a : QPair} (h : qLT qZero a = true) : 0 < a.num := by
  have hc : qZero.num * Int.ofNat a.den < a.num * Int.ofNat qZero.den :=
    of_decide_eq_true (by simpa only [qLT] using! h)
  simpa [qZero] using! hc

theorem toRat_qInv_pos (a : QPair) (h : qLT qZero a = true) :
    (qInv a).toRat = a.toRat⁻¹ := by
  have hn := qLT_zero_num h
  have hnat : (a.num.toNat : ℚ) = (a.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn.le
  simp [qInv, hn, QPair.toRat, hnat, inv_div]

theorem qValid_qInv_pos (a : QPair) (h : qLT qZero a = true) :
    qValid (qInv a) = true := by
  have hn := qLT_zero_num h
  simp only [qInv, if_pos hn, qValid, decide_eq_true_eq]
  omega

theorem toRat_qDiv_pos (a b : QPair) (h : qLT qZero b = true) :
    (qDiv a b).toRat = a.toRat / b.toRat := by
  rw [qDiv, toRat_qMul, toRat_qInv_pos b h]
  rfl

theorem qValid_qDiv_pos {a b : QPair} (ha : qValid a = true)
    (hb : qLT qZero b = true) : qValid (qDiv a b) = true := by
  exact qValid_qMul ha (qValid_qInv_pos b hb)

theorem toRat_qSub (a b : QPair)
    (ha : qValid a = true) (hb : qValid b = true) :
    (qSub a b).toRat = a.toRat - b.toRat := by
  rw [qSub, toRat_qAdd _ _ ha (qValid_qNeg hb), toRat_qNeg]
  ring

theorem qValid_qSub {a b : QPair} (ha : qValid a = true)
    (hb : qValid b = true) : qValid (qSub a b) = true := by
  exact qValid_qAdd ha (qValid_qNeg hb)

theorem toRat_qPow (a : QPair) (n : ℕ) :
    (qPow a n).toRat = a.toRat ^ n := by
  induction n with
  | zero => simpa only [qPow, pow_zero] using! qOne_toRat
  | succ n ih => simp only [qPow, toRat_qMul, ih, pow_succ]

theorem qValid_qPow {a : QPair} (ha : qValid a = true) (n : ℕ) :
    qValid (qPow a n) = true := by
  induction n with
  | zero => exact qValid_qOne
  | succ n ih => exact qValid_qMul ih ha

theorem foldl_qAdd_valid (xs : List ℕ) (f : ℕ → QPair)
    (hf : ∀ i ∈ xs, qValid (f i) = true)
    (acc : QPair) (hacc : qValid acc = true) :
    qValid (xs.foldl (fun q i => qAdd q (f i)) acc) = true := by
  induction xs generalizing acc with
  | nil => simpa using! hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hf j (by simp [hj])
      · exact qValid_qAdd hacc (hf i (by simp))

theorem foldl_qAdd_toRat (xs : List ℕ) (f : ℕ → QPair)
    (hf : ∀ i ∈ xs, qValid (f i) = true)
    (acc : QPair) (hacc : qValid acc = true) :
    (xs.foldl (fun q i => qAdd q (f i)) acc).toRat =
      acc.toRat + (xs.map fun i => (f i).toRat).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons i xs ih =>
      have hfi : qValid (f i) = true := hf i (by simp)
      have hxs : ∀ j ∈ xs, qValid (f j) = true := by
        intro j hj
        exact hf j (by simp [hj])
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih hxs (qAdd acc (f i)) (qValid_qAdd hacc hfi),
        toRat_qAdd acc (f i) hacc hfi]
      ring

theorem range_map_sum_eq (f : ℕ → ℚ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

private def natDen (n : ℕ) : QPair := ⟨Int.ofNat (n + 1), 1⟩
private def logTerm (r : QPair) (i : ℕ) : QPair :=
  qDiv (qPow (qSub qOne r) (i + 1)) (natDen i)

private theorem natDen_pos (n : ℕ) : qLT qZero (natDen n) = true := by
  simp [qLT, qZero, natDen]

private theorem natDen_toRat (n : ℕ) :
    (natDen n).toRat = ((n + 1 : ℕ) : ℚ) := by
  simp [natDen, QPair.toRat]

private theorem logTerm_valid (r : QPair) (hr : qValid r = true) (i : ℕ) :
    qValid (logTerm r i) = true := by
  exact qValid_qDiv_pos
    (qValid_qPow (qValid_qSub qValid_qOne hr) (i + 1)) (natDen_pos i)

private theorem logTerm_toRat (r : QPair) (hr : qValid r = true) (i : ℕ) :
    (logTerm r i).toRat =
      (1 - r.toRat) ^ (i + 1) / (((i + 1 : ℕ) : ℚ)) := by
  rw [logTerm, toRat_qDiv_pos _ _ (natDen_pos i),
    toRat_qPow, toRat_qSub _ _ qValid_qOne hr,
    qOne_toRat, natDen_toRat]

theorem logPartial_toRat (r : QPair) (hr : qValid r = true) (n : ℕ) :
    (logPartial r n).toRat = ParameterFamily.logPartial r.toRat n := by
  change ((List.range n).foldl (fun acc i => qAdd acc (logTerm r i)) qZero).toRat = _
  rw [foldl_qAdd_toRat (List.range n) (logTerm r)
    (by intro i hi; exact logTerm_valid r hr i) qZero qValid_qZero]
  rw [qZero_toRat, zero_add, range_map_sum_eq]
  unfold ParameterFamily.logPartial
  apply Finset.sum_congr rfl
  intro i _
  exact logTerm_toRat r hr i

theorem logError_toRat (r : QPair) (hr : qValid r = true)
    (hrpos : qLT qZero r = true) (n : ℕ) :
    (logError r n).toRat = ParameterFamily.logError r.toRat n := by
  rw [logError, toRat_qDiv_pos _ _ hrpos,
    toRat_qPow, toRat_qSub _ _ qValid_qOne hr, qOne_toRat]
  rfl

theorem logPartial_valid (r : QPair) (hr : qValid r = true) (n : ℕ) :
    qValid (logPartial r n) = true := by
  change qValid ((List.range n).foldl (fun acc i => qAdd acc (logTerm r i)) qZero) = true
  exact foldl_qAdd_valid (List.range n) (logTerm r)
    (by intro i hi; exact logTerm_valid r hr i) qZero qValid_qZero

theorem logError_valid (r : QPair) (hr : qValid r = true)
    (hrpos : qLT qZero r = true) (n : ℕ) :
    qValid (logError r n) = true := by
  exact qValid_qDiv_pos
    (qValid_qPow (qValid_qSub qValid_qOne hr) (n + 1)) hrpos

theorem reducedLogBounds_toBounds (r : QPair) (hr : qValid r = true)
    (hrpos : qLT qZero r = true) (n : ℕ) :
    (reducedLogBounds r n).toBounds =
      ParameterFamily.reducedLogBounds r.toRat n := by
  let p := logPartial r n
  let e := logError r n
  have hp : qValid p = true := logPartial_valid r hr n
  have he : qValid e = true := logError_valid r hr hrpos n
  apply congrArg₂ RationalBounds.mk
  · change (qSub (qNeg p) e).toRat =
      -ParameterFamily.logPartial r.toRat n - ParameterFamily.logError r.toRat n
    rw [toRat_qSub _ _ (qValid_qNeg hp) he, toRat_qNeg,
      logPartial_toRat r hr n, logError_toRat r hr hrpos n]
  · change (qAdd (qNeg p) e).toRat =
      -ParameterFamily.logPartial r.toRat n + ParameterFamily.logError r.toRat n
    rw [toRat_qAdd _ _ (qValid_qNeg hp) he, toRat_qNeg,
      logPartial_toRat r hr n, logError_toRat r hr hrpos n]

private theorem sign_of_mod_two (i : ℕ) :
    (if i % 2 == 0 then (1 : ℚ) else -1) = (-1 : ℚ) ^ i := by
  have hdecomp : i = 2 * (i / 2) + i % 2 := by omega
  rw [hdecomp]
  by_cases h : i % 2 = 0
  · simp [h, pow_mul]
  · have h1 : i % 2 = 1 := by omega
    simp [h1, pow_add, pow_mul]

private def atanTerm (r : QPair) (i : ℕ) : QPair :=
  let term := qDiv (qPow r (2 * i + 1)) (natDen (2 * i))
  if i % 2 == 0 then term else qNeg term

private theorem atanTerm_valid (r : QPair) (hr : qValid r = true) (i : ℕ) :
    qValid (atanTerm r i) = true := by
  unfold atanTerm
  split_ifs
  · exact qValid_qDiv_pos (qValid_qPow hr (2 * i + 1)) (natDen_pos (2 * i))
  · exact qValid_qNeg
      (qValid_qDiv_pos (qValid_qPow hr (2 * i + 1)) (natDen_pos (2 * i)))

private theorem atanTerm_toRat (r : QPair) (i : ℕ) :
    (atanTerm r i).toRat =
      (-1 : ℚ) ^ i * (r.toRat ^ (2 * i + 1) / (((2 * i + 1 : ℕ) : ℚ))) := by
  have hterm :
      (qDiv (qPow r (2 * i + 1)) (natDen (2 * i))).toRat =
        r.toRat ^ (2 * i + 1) / (((2 * i + 1 : ℕ) : ℚ)) := by
    rw [toRat_qDiv_pos _ _ (natDen_pos (2 * i)), toRat_qPow, natDen_toRat]
  by_cases h : i % 2 = 0
  · have hs : (-1 : ℚ) ^ i = 1 := by rw [← sign_of_mod_two]; simp [h]
    simpa [atanTerm, h, hs] using! hterm
  · have hs : (-1 : ℚ) ^ i = -1 := by rw [← sign_of_mod_two]; simp [h]
    simpa [atanTerm, h, hs, toRat_qNeg] using! congrArg Neg.neg hterm

theorem atanPartial_toRat (r : QPair) (hr : qValid r = true) (n : ℕ) :
    (atanPartial r n).toRat = ParameterFamily.arctanPartial r.toRat n := by
  change ((List.range n).foldl (fun acc i => qAdd acc (atanTerm r i)) qZero).toRat = _
  rw [foldl_qAdd_toRat (List.range n) (atanTerm r)
    (by intro i hi; exact atanTerm_valid r hr i) qZero qValid_qZero]
  rw [qZero_toRat, zero_add, range_map_sum_eq]
  unfold ParameterFamily.arctanPartial
  apply Finset.sum_congr rfl
  intro i _
  exact atanTerm_toRat r i

theorem atanPartial_valid (r : QPair) (hr : qValid r = true) (n : ℕ) :
    qValid (atanPartial r n) = true := by
  change qValid ((List.range n).foldl (fun acc i => qAdd acc (atanTerm r i)) qZero) = true
  exact foldl_qAdd_valid (List.range n) (atanTerm r)
    (by intro i hi; exact atanTerm_valid r hr i) qZero qValid_qZero

theorem smallAtanBounds_toBounds (r : QPair) (hr : qValid r = true) (k : ℕ) :
    (smallAtanBounds r k).toBounds = ParameterFamily.smallArctanBounds r.toRat k := by
  exact congrArg₂ RationalBounds.mk
    (atanPartial_toRat r hr (2 * k))
    (atanPartial_toRat r hr (2 * k + 1))

#print axioms reducedLogBounds_toBounds
#print axioms smallAtanBounds_toBounds

end Li2Unified.Proofs.Potential.KernelReflectionSelf

end


end
