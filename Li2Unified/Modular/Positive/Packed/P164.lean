module
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P106
public import Li2Unified.Modular.Positive.Packed.P107
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section

section
/-! Soundness bridge from the integer-pair checker to the existing real
interval operations. The checker itself imports only Init. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf

open Li2Unified.ParameterFamily

def QPair.toRat (q : QPair) : ℚ := (q.num : ℚ) / (q.den : ℚ)
def I.toBounds (i : I) : RationalBounds := ⟨i.lo.toRat, i.hi.toRat⟩

theorem qValid_pos {q : QPair} (h : qValid q = true) : 0 < q.den := by
  exact of_decide_eq_true (by simpa only [qValid] using h)

theorem qLE_sound {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (h : qLE a b = true) : a.toRat ≤ b.toRat := by
  have ha' : (0 : ℚ) < a.den := by exact_mod_cast qValid_pos ha
  have hb' : (0 : ℚ) < b.den := by exact_mod_cast qValid_pos hb
  have hc : a.num * Int.ofNat b.den ≤ b.num * Int.ofNat a.den :=
    of_decide_eq_true (by simpa only [qLE] using h)
  have hc' : (a.num : ℚ) * (b.den : ℚ) ≤ (b.num : ℚ) * (a.den : ℚ) := by
    exact_mod_cast hc
  exact (div_le_div_iff₀ ha' hb').mpr hc'

theorem qLT_sound {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (h : qLT a b = true) : a.toRat < b.toRat := by
  have ha' : (0 : ℚ) < a.den := by exact_mod_cast qValid_pos ha
  have hb' : (0 : ℚ) < b.den := by exact_mod_cast qValid_pos hb
  have hc : a.num * Int.ofNat b.den < b.num * Int.ofNat a.den :=
    of_decide_eq_true (by simpa only [qLT] using h)
  have hc' : (a.num : ℚ) * (b.den : ℚ) < (b.num : ℚ) * (a.den : ℚ) := by
    exact_mod_cast hc
  exact (div_lt_div_iff₀ ha' hb').mpr hc'

theorem qEq_sound {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (h : qEq a b = true) : a.toRat = b.toRat := by
  have h' : qLE a b = true ∧ qLE b a = true := by
    simpa only [qEq, Bool.and_eq_true] using h
  exact le_antisymm (qLE_sound ha hb h'.1) (qLE_sound hb ha h'.2)

theorem qLE_complete {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (h : a.toRat ≤ b.toRat) : qLE a b = true := by
  have ha' : (0 : ℚ) < a.den := by exact_mod_cast qValid_pos ha
  have hb' : (0 : ℚ) < b.den := by exact_mod_cast qValid_pos hb
  have hc : (a.num : ℚ) * (b.den : ℚ) ≤ (b.num : ℚ) * (a.den : ℚ) :=
    (div_le_div_iff₀ ha' hb').mp h
  have hc' : a.num * Int.ofNat b.den ≤ b.num * Int.ofNat a.den := by
    exact_mod_cast hc
  exact decide_eq_true hc'

theorem toRat_qAdd (a b : QPair)
    (ha : qValid a = true) (hb : qValid b = true) :
    (qAdd a b).toRat = a.toRat + b.toRat := by
  have ha0 : (a.den : ℚ) ≠ 0 := (by exact_mod_cast qValid_pos ha : (0 : ℚ) < a.den).ne'
  have hb0 : (b.den : ℚ) ≠ 0 := (by exact_mod_cast qValid_pos hb : (0 : ℚ) < b.den).ne'
  simp only [qAdd, QPair.toRat, Int.cast_add, Int.cast_mul, Nat.cast_mul]
  field_simp
  norm_cast

theorem toRat_qNeg (a : QPair) :
    (qNeg a).toRat = -a.toRat := by
  simp [qNeg, QPair.toRat, neg_div]

theorem toRat_qMul (a b : QPair) :
    (qMul a b).toRat = a.toRat * b.toRat := by
  simp [qMul, QPair.toRat, mul_div_mul_comm]

theorem qValid_qAdd {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true) :
    qValid (qAdd a b) = true := by
  simp only [qValid, qAdd, decide_eq_true_eq]
  exact Nat.mul_pos (qValid_pos ha) (qValid_pos hb)

theorem qValid_qNeg {a : QPair} (ha : qValid a = true) :
    qValid (qNeg a) = true := by
  simpa only [qValid, qNeg] using ha

theorem qValid_qMul {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true) :
    qValid (qMul a b) = true := by
  simp only [qValid, qMul, decide_eq_true_eq]
  exact Nat.mul_pos (qValid_pos ha) (qValid_pos hb)

theorem toRat_qMin (a b : QPair)
    (ha : qValid a = true) (hb : qValid b = true) :
    (qMin a b).toRat = min a.toRat b.toRat := by
  unfold qMin
  split_ifs with h
  · exact (min_eq_left (qLE_sound ha hb h)).symm
  · have hn : ¬ a.toRat ≤ b.toRat := by
      intro hab
      exact h (qLE_complete ha hb hab)
    exact (min_eq_right (le_of_not_ge hn)).symm

theorem toRat_qMax (a b : QPair)
    (ha : qValid a = true) (hb : qValid b = true) :
    (qMax a b).toRat = max a.toRat b.toRat := by
  unfold qMax
  split_ifs with h
  · exact (max_eq_right (qLE_sound ha hb h)).symm
  · have hn : ¬ a.toRat ≤ b.toRat := by
      intro hab
      exact h (qLE_complete ha hb hab)
    exact (max_eq_left (le_of_not_ge hn)).symm

theorem qValid_qMin {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true) :
    qValid (qMin a b) = true := by
  unfold qMin
  split_ifs <;> assumption

theorem qValid_qMax {a b : QPair}
    (ha : qValid a = true) (hb : qValid b = true) :
    qValid (qMax a b) = true := by
  unfold qMax
  split_ifs <;> assumption

theorem validI_parts {a : I} (h : validI a = true) :
    qValid a.lo = true ∧ qValid a.hi = true ∧ qLE a.lo a.hi = true := by
  simp only [validI, Bool.and_eq_true] at h
  rcases h with ⟨⟨hlo, hhi⟩, hle⟩
  exact ⟨hlo, hhi, hle⟩

theorem encloses_parts {out candidate : I} (h : encloses out candidate = true) :
    validI out = true ∧ validI candidate = true ∧
    qLE out.lo candidate.lo = true ∧ qLE candidate.hi out.hi = true := by
  simp only [encloses, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨ho, hc⟩, hlo⟩, hhi⟩
  exact ⟨ho, hc, hlo, hhi⟩

theorem encloses_sound {out candidate : I} (h : encloses out candidate = true) :
    out.toBounds.lower ≤ candidate.toBounds.lower ∧
    candidate.toBounds.upper ≤ out.toBounds.upper := by
  obtain ⟨ho, hc, hlow, hhigh⟩ := encloses_parts h
  obtain ⟨holo, hohi, _⟩ := validI_parts ho
  obtain ⟨hclo, hchi, _⟩ := validI_parts hc
  exact ⟨qLE_sound holo hclo hlow, qLE_sound hchi hohi hhigh⟩

theorem toBounds_add (a b : I)
    (ha : validI a = true) (hb : validI b = true) :
    (add a b).toBounds = RationalBounds.add a.toBounds b.toBounds := by
  obtain ⟨halo, hahi, _⟩ := validI_parts ha
  obtain ⟨hblo, hbhi, _⟩ := validI_parts hb
  exact congrArg₂ RationalBounds.mk
    (toRat_qAdd a.lo b.lo halo hblo)
    (toRat_qAdd a.hi b.hi hahi hbhi)

theorem toBounds_neg (a : I) :
    (neg a).toBounds = RationalBounds.neg a.toBounds := by
  exact congrArg₂ RationalBounds.mk (toRat_qNeg a.hi) (toRat_qNeg a.lo)

theorem toBounds_mul (a b : I)
    (ha : validI a = true) (hb : validI b = true) :
    (mul a b).toBounds = RationalBounds.mul a.toBounds b.toBounds := by
  obtain ⟨halo, hahi, _⟩ := validI_parts ha
  obtain ⟨hblo, hbhi, _⟩ := validI_parts hb
  have hll := qValid_qMul halo hblo
  have hlu := qValid_qMul halo hbhi
  have hul := qValid_qMul hahi hblo
  have huu := qValid_qMul hahi hbhi
  have hlow :
      (qMin (qMin (qMul a.lo b.lo) (qMul a.lo b.hi))
        (qMin (qMul a.hi b.lo) (qMul a.hi b.hi))).toRat =
      min (min (a.lo.toRat * b.lo.toRat) (a.lo.toRat * b.hi.toRat))
        (min (a.hi.toRat * b.lo.toRat) (a.hi.toRat * b.hi.toRat)) := by
    rw [toRat_qMin _ _ (qValid_qMin hll hlu) (qValid_qMin hul huu),
      toRat_qMin _ _ hll hlu, toRat_qMin _ _ hul huu,
      toRat_qMul, toRat_qMul, toRat_qMul, toRat_qMul]
  have hhigh :
      (qMax (qMax (qMul a.lo b.lo) (qMul a.lo b.hi))
        (qMax (qMul a.hi b.lo) (qMul a.hi b.hi))).toRat =
      max (max (a.lo.toRat * b.lo.toRat) (a.lo.toRat * b.hi.toRat))
        (max (a.hi.toRat * b.lo.toRat) (a.hi.toRat * b.hi.toRat)) := by
    rw [toRat_qMax _ _ (qValid_qMax hll hlu) (qValid_qMax hul huu),
      toRat_qMax _ _ hll hlu, toRat_qMax _ _ hul huu,
      toRat_qMul, toRat_qMul, toRat_qMul, toRat_qMul]
  exact congrArg₂ RationalBounds.mk hlow hhigh

#print axioms toBounds_mul
#print axioms encloses_sound

end Li2Unified.Proofs.Potential.KernelReflectionSelf

end

section
/-! Generic sound interval bounds for H(x)=x log|x|, including its cusp. -/
namespace Li2Unified.Proofs.Potential
noncomputable section
open Li2Unified.ParameterFamily

def mulLogAbs (x : ℝ) : ℝ := x*Real.log |x|

lemma mulLogAbs_odd (x : ℝ) : mulLogAbs (-x) = -mulLogAbs x := by
  simp only [mulLogAbs, abs_neg, neg_mul]

lemma mulLogAbs_nonneg (x : ℝ) (hx : 0 ≤ x) :
    mulLogAbs x = x*Real.log x := by
  simp only [mulLogAbs, abs_of_nonneg hx]

lemma mulLogAbs_antitone_quarter {a x b : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ 1/4) :
    b*Real.log b ≤ mulLogAbs x ∧ mulLogAbs x ≤ a*Real.log a := by
  have hx : 0 ≤ x := ha.trans hax
  rw [mulLogAbs_nonneg x hx]
  constructor
  · exact mul_log_antitone_quarter ⟨hx, hxb.trans hb⟩
      ⟨hx.trans hxb, hb⟩ hxb
  · exact mul_log_antitone_quarter ⟨ha, hax.trans (hxb.trans hb)⟩
      ⟨hx, hxb.trans hb⟩ hax

lemma mulLogAbs_cross_zero {x r : ℝ} (hx : |x| ≤ r) (hr : r ≤ 1/4) :
    |mulLogAbs x| ≤ -r*Real.log r := by
  simpa only [mulLogAbs, Real.log_abs] using abs_mul_log_le_radius x r hx hr

end
end Li2Unified.Proofs.Potential

end

section
/-! Semantic and list-induction layer for the integer-pair reflection checker. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section
open Li2Unified.ParameterFamily

def evalOp (x : ℝ) (v : ℕ → ℝ) : Op → ℝ
  | .rat q => (q.toRat : ℝ)
  | .var => x
  | .logTwo => Real.log 2
  | .pi => Real.pi
  | .logAtom q _ _ _ => Real.log (q.toRat : ℝ)
  | .atanSmall q _ => Real.arctan (q.toRat : ℝ)
  | .atanHalf q _ _ => Real.arctan (q.toRat : ℝ)
  | .atanInverse q _ _ => Real.arctan (q.toRat : ℝ)
  | .alias a => v a
  | .add a b => v a + v b
  | .neg a => -v a
  | .mul a b => v a * v b
  | .log a _ _ => Real.log (v a)
  | .atan a _ _ => Real.arctan (v a)
  | .hPositiveProduct a _ => mulLogAbs (v a)
  | .hQuarter a _ _ => mulLogAbs (v a)
  | .hCross a _ _ => mulLogAbs (v a)

def StepSem (x : ℝ) (v : ℕ → ℝ) (s : Step) : Prop :=
  v s.id = evalOp x v s.op

def EnvGood (x : ℝ) (v : ℕ → ℝ) (env : List Step) : Prop :=
  ∀ s ∈ env, validI s.out = true ∧
    s.out.toBounds.Contains (v s.id) ∧ StepSem x v s

end
end Li2Unified.Proofs.Potential.KernelReflectionSelf

end

section
/-! Real semantics of the expression program reified from a checked trace. -/
namespace Li2Unified.Proofs.Potential.ReflectionProgram

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.ParameterFamily

noncomputable section

def Expr.denote (x : ℝ) : Expr → ℝ
  | .rat q => (q.toRat : ℝ)
  | .var => x
  | .logTwo => Real.log 2
  | .pi => Real.pi
  | .add a b => a.denote x + b.denote x
  | .neg a => -a.denote x
  | .mul a b => a.denote x * b.denote x
  | .log a => Real.log (a.denote x)
  | .atan a => Real.arctan (a.denote x)
  | .H a => mulLogAbs (a.denote x)

def valuation (x : ℝ) (env : ExprEnv) (id : ℕ) : ℝ :=
  ((lookupExpr env id).map (Expr.denote x)).getD 0

theorem valuation_of_lookupExpr {x : ℝ} {env : ExprEnv} {id : ℕ} {e : Expr}
    (h : lookupExpr env id = some e) : valuation x env id = e.denote x := by
  simp [valuation, h]

theorem lookupExpr_cons (env : ExprEnv) (s : Step) (e : Expr) (id : ℕ) :
    lookupExpr ((s, e) :: env) id =
      if s.id == id then some e else lookupExpr env id := by
  by_cases h : s.id = id
  · simp [lookupExpr, List.find?, h]
  · have hb : (s.id == id) = false := by
      simpa using (beq_eq_false_iff_ne.mpr h)
    simp [lookupExpr, List.find?, hb]

theorem lookupExpr_cons_preserve (env : ExprEnv) (s : Step) (e : Expr)
    (hfresh : lookupExpr env s.id = none) {id : ℕ} {ei : Expr}
    (h : lookupExpr env id = some ei) :
    lookupExpr ((s, e) :: env) id = some ei := by
  rw [lookupExpr_cons]
  by_cases heq : s.id = id
  · subst id
    rw [hfresh] at h
    cases h
  · simp [heq, h]

theorem reifyGo_lookup_preserve {env final : ExprEnv} {ss : List Step}
    (h : reifyGo env ss = some final) :
    ∀ id ei, lookupExpr env id = some ei → lookupExpr final id = some ei := by
  induction ss generalizing env final with
  | nil =>
      simp [reifyGo] at h
      subst final
      intro id ei hi
      exact hi
  | cons s ss ih =>
      cases hfresh : lookupExpr env s.id with
      | some _ => simp [reifyGo, hfresh] at h
      | none =>
          cases hop : reifyOp env s.op with
          | none => simp [reifyGo, hfresh, hop] at h
          | some e =>
              have ht : reifyGo ((s, e) :: env) ss = some final := by
                simpa [reifyGo, hfresh, hop] using h
              intro id ei hi
              exact ih ht id ei (lookupExpr_cons_preserve env s e hfresh hi)

theorem reifyOp_denote {x : ℝ} {env final : ExprEnv} {op : Op} {e : Expr}
    (hpres : ∀ id ei, lookupExpr env id = some ei →
      lookupExpr final id = some ei)
    (hop : reifyOp env op = some e) :
    e.denote x = evalOp x (valuation x final) op := by
  have hval (id : ℕ) (ei : Expr) (h : lookupExpr env id = some ei) :
      valuation x final id = ei.denote x :=
    valuation_of_lookupExpr (hpres id ei h)
  cases op with
  | rat q =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | var =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | logTwo =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | pi =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | logAtom q u rho k =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | atanSmall q terms =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | atanHalf q r terms =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | atanInverse q r inverseNode =>
      simp only [reifyOp, Option.some.injEq] at hop
      subst e
      rfl
  | «alias» a =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          simpa only [evalOp] using (hval a ea ha).symm
  | add a b =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          cases hb : lookupExpr env b with
          | none => simp [reifyOp, ha, hb] at hop
          | some eb =>
              simp [reifyOp, ha, hb] at hop
              subst e
              rw [evalOp, hval a ea ha, hval b eb hb]
              rfl
  | neg a =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          rw [evalOp, hval a ea ha]
          rfl
  | mul a b =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          cases hb : lookupExpr env b with
          | none => simp [reifyOp, ha, hb] at hop
          | some eb =>
              simp [reifyOp, ha, hb] at hop
              subst e
              rw [evalOp, hval a ea ha, hval b eb hb]
              rfl
  | log a lo hi =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          rw [evalOp, hval a ea ha]
          rfl
  | atan a lo hi =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          rw [evalOp, hval a ea ha]
          rfl
  | hPositiveProduct a witness =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          rw [evalOp, hval a ea ha]
          rfl
  | hQuarter a lo hi =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          rw [evalOp, hval a ea ha]
          rfl
  | hCross a logRadius radius =>
      cases ha : lookupExpr env a with
      | none => simp [reifyOp, ha] at hop
      | some ea =>
          simp [reifyOp, ha] at hop
          subst e
          rw [evalOp, hval a ea ha]
          rfl

theorem reifyGo_stepSem {x : ℝ} {env final : ExprEnv} {steps : List Step}
    (h : reifyGo env steps = some final) :
    ∀ s ∈ steps, StepSem x (valuation x final) s := by
  induction steps generalizing env final with
  | nil =>
      intro s hs
      simp at hs
  | cons s ss ih =>
      cases hfresh : lookupExpr env s.id with
      | some _ => simp [reifyGo, hfresh] at h
      | none =>
          cases hop : reifyOp env s.op with
          | none => simp [reifyGo, hfresh, hop] at h
          | some e =>
              have ht : reifyGo ((s, e) :: env) ss = some final := by
                simpa [reifyGo, hfresh, hop] using h
              have hpres := reifyGo_lookup_preserve ht
              have hpres0 : ∀ id ei, lookupExpr env id = some ei →
                  lookupExpr final id = some ei := by
                intro id ei hi
                exact hpres id ei (lookupExpr_cons_preserve env s e hfresh hi)
              have hnew : lookupExpr final s.id = some e := by
                apply hpres s.id e
                simp [lookupExpr_cons]
              intro t hmem
              rcases List.mem_cons.mp hmem with rfl | htail
              · unfold StepSem
                rw [valuation_of_lookupExpr hnew]
                exact reifyOp_denote hpres0 hop
              · exact ih ht t htail

theorem reifyTrace_stepSem {x : ℝ} {steps : List Step} {env : ExprEnv}
    (h : reifyTrace steps = some env) :
    ∀ s ∈ steps, StepSem x (valuation x env) s := by
  exact reifyGo_stepSem (by simpa only [reifyTrace] using h)

#print axioms valuation_of_lookupExpr
#print axioms reifyTrace_stepSem

end
end Li2Unified.Proofs.Potential.ReflectionProgram

end

section
namespace Li2Unified.Proofs.Potential.CompactAffine

noncomputable section

/-- The smooth potential atom contributed by a ray or vertical layer. -/
def F (r t : ℝ) : ℝ :=
  r * Real.log (r ^ 2 + t ^ 2) / 2 - t * Real.arctan (t / r)

theorem F_hasDerivAt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasDerivAt (F r) (-Real.arctan (t / r)) t := by
  have hr0 : r ≠ 0 := hr.ne'
  have hq : t ^ 2 + r ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hr))
  have hlog : HasDerivAt (fun s : ℝ => Real.log (r ^ 2 + s ^ 2))
      (2 * t / (r ^ 2 + t ^ 2)) t := by
    convert (((hasDerivAt_id t).pow 2).add_const (r ^ 2)).log hq using 1
    <;> norm_num
    <;> ring
  have hquot : 1 + (t / r) ^ 2 = (r ^ 2 + t ^ 2) / r ^ 2 := by
    field_simp [hr0]
  have hatan : HasDerivAt (fun s : ℝ => Real.arctan (s / r))
      (r / (r ^ 2 + t ^ 2)) t := by
    convert ((hasDerivAt_id t).div_const r).arctan using 1
    dsimp only [id_eq]
    rw [hquot]
    field_simp [hr0, hq]
  have h := (((hlog.const_mul r).div_const 2).sub ((hasDerivAt_id t).mul hatan))
  convert h using 1
  dsimp only [F, Pi.sub_apply, Pi.mul_apply, id_eq]
  field_simp [hr0, hq]
  <;> ring

theorem F_deriv {r : ℝ} (hr : 0 < r) (t : ℝ) :
    deriv (F r) t = -Real.arctan (t / r) :=
  (F_hasDerivAt hr t).deriv

theorem F_concaveOn {r : ℝ} (hr : 0 < r) :
    ConcaveOn ℝ Set.univ (F r) := by
  have hdiff : Differentiable ℝ (F r) :=
    fun t => (F_hasDerivAt hr t).differentiableAt
  have hanti : Antitone (deriv (F r)) := by
    intro a b hab
    rw [F_deriv hr a, F_deriv hr b]
    exact neg_le_neg (Real.arctan_mono (div_le_div_of_nonneg_right hab hr.le))
  exact Antitone.concaveOn_univ_of_deriv hdiff hanti

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.F_hasDerivAt
#print axioms Li2Unified.Proofs.Potential.CompactAffine.F_concaveOn

end


end
