module
public import Li2Unified.Modular.Positive.Packed.P164
public import Li2Unified.Modular.Positive.Packed.P172
public import Li2Unified.Modular.Positive.Packed.P170
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P167

set_option backward.privateInPublic true

@[expose] public section

section
/-! One bridge from a checked trace and reified expression to its real value. -/
namespace Li2Unified.Proofs.Potential.ReflectionProgram

open Li2Unified.Proofs.Potential.KernelReflectionSelf

noncomputable section

theorem checkedExpr_sound {x : ℝ} {domain : I} {steps : List Step}
    {env : ExprEnv} {id : ℕ} {e : Expr} {out : I}
    (hx : domain.toBounds.Contains x)
    (hcheck : Domain.checkTrace domain steps = true)
    (hreify : reifyTrace steps = some env)
    (hexpr : lookupExpr env id = some e)
    (hlookup : KernelReflectionSelf.lookup steps.reverse id = some out) :
    validI out = true ∧ out.toBounds.Contains (e.denote x) := by
  have hsem : ∀ s ∈ steps, StepSem x (valuation x env) s :=
    reifyTrace_stepSem hreify
  obtain ⟨hvalid, hbound⟩ :=
    Domain.checkTrace_lookup_sound hx hsem hcheck hlookup
  rw [valuation_of_lookupExpr hexpr] at hbound
  exact ⟨hvalid, hbound⟩

#print axioms checkedExpr_sound

end
end Li2Unified.Proofs.Potential.ReflectionProgram

end

section
/-! Fixed constant nodes for the kernel-reflection trace. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf

open Li2Unified.ParameterFamily

theorem contains_rat_point (q : QPair) :
    (point q).toBounds.Contains (q.toRat : ℝ) := by
  exact RationalBounds.contains_point q.toRat

theorem contains_logTwo :
    logTwoBounds.toBounds.Contains (Real.log 2) := by
  rw [logTwoBounds_toBounds]
  exact ParameterFamily.contains_logTwo

theorem contains_pi : piBounds.toBounds.Contains Real.pi := by
  rw [piBounds_toBounds]
  exact ParameterFamily.contains_pi

#print axioms contains_rat_point
#print axioms contains_logTwo
#print axioms contains_pi

end Li2Unified.Proofs.Potential.KernelReflectionSelf

end

section
/-! Soundness of one cached point check for a compact affine trace. -/
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram

noncomputable section

theorem closeAt_denote (q : QPair) (e : Expr) (x : ℝ) :
    (closeAt q e).denote x = e.denote (q.toRat : ℝ) := by
  induction e <;> simp [closeAt, Expr.denote, *]

theorem qAbs_toRat (u : QPair) (hu : qValid u = true) :
    (qAbs u).toRat = |u.toRat| := by
  by_cases hle : qLE qZero u = true
  · have hnon : (0 : ℚ) ≤ u.toRat := by
      simpa only [qZero_toRat] using! qLE_sound qValid_qZero hu hle
    simp [qAbs, hle, abs_of_nonneg hnon]
  · have hneg : u.toRat < 0 := by
      by_contra hnot
      have hnon : (0 : ℚ) ≤ u.toRat := le_of_not_gt hnot
      have hh : qLE qZero u = true :=
        qLE_complete qValid_qZero hu (by simpa only [qZero_toRat] using! hnon)
      exact hle hh
    simp [qAbs, hle, toRat_qNeg, abs_of_neg hneg]

theorem argument_valid (shift x : QPair) (negative : Bool)
    (hs : qValid shift = true) (hx : qValid x = true) :
    qValid (argument shift x negative) = true := by
  cases negative with
  | false => exact qValid_qAdd hs hx
  | true => exact qValid_qSub hs hx

theorem argument_toRat (shift x : QPair) (negative : Bool)
    (hs : qValid shift = true) (hx : qValid x = true) :
    (argument shift x negative).toRat =
      shift.toRat + (if negative then -x.toRat else x.toRat) := by
  cases negative with
  | false => simpa [argument] using! toRat_qAdd shift x hs hx
  | true => simpa [argument, sub_eq_add_neg] using! toRat_qSub shift x hs hx

private theorem hPoint_denote (c u : QPair) (hu : qValid u = true) :
    (if qEq u qZero then Expr.rat qZero
      else Expr.mul (.rat c) (.mul (.rat u) (.log (.rat (qAbs u))))).denote 0 =
      (c.toRat : ℝ) * Li2Unified.Stage0.HalfPotentialExpressions.H (u.toRat : ℝ) := by
  by_cases hz : qEq u qZero = true
  · have hu0 : u.toRat = 0 := by
      simpa only [qZero_toRat] using! qEq_sound hu qValid_qZero hz
    simp [hz, Expr.denote, qZero_toRat, hu0,
      Li2Unified.Stage0.HalfPotentialExpressions.H]
  · have habs : ((qAbs u).toRat : ℝ) = |(u.toRat : ℝ)| := by
      rw [qAbs_toRat u hu]
      exact_mod_cast (show (|u.toRat| : ℚ) = |u.toRat| by rfl)
    simp [hz, Expr.denote, habs,
      Li2Unified.Stage0.HalfPotentialExpressions.H]

theorem pointExpr_denote_eq_eval (t : Term) (x : QPair)
    (ht : validTerm t = true) (hx : qValid x = true) :
    (pointExpr t x).denote 0 = t.eval (x.toRat : ℝ) := by
  cases t with
  | constant e =>
      simp [pointExpr, Term.eval, closeAt_denote, qZero_toRat]
  | linear e =>
      simp [pointExpr, Term.eval, Expr.denote, closeAt_denote, qZero_toRat]
  | H c shift negative =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨_, hs⟩ := ht
      have hu : qValid (argument shift x negative) = true :=
        argument_valid shift x negative hs hx
      have harg : ((argument shift x negative).toRat : ℝ) =
          (shift.toRat : ℝ) +
            (if negative then -(x.toRat : ℝ) else (x.toRat : ℝ)) := by
        cases negative with
        | false => simp [argument, toRat_qAdd shift x hs hx]
        | true => simp [argument, toRat_qSub shift x hs hx, sub_eq_add_neg]
      calc
        (pointExpr (Term.H c shift negative) x).denote 0 =
            (c.toRat : ℝ) *
              Li2Unified.Stage0.HalfPotentialExpressions.H
                ((argument shift x negative).toRat : ℝ) := by
                  simpa only [pointExpr, argument] using! hPoint_denote c
                    (argument shift x negative) hu
        _ = (Term.H c shift negative).eval (x.toRat : ℝ) := by
              rw [harg]
              rfl
  | F c r =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨⟨_, hr⟩, hrpos⟩ := ht
      have hhalf : (qDiv r ⟨2, 1⟩).toRat = r.toRat / 2 := by
        rw [toRat_qDiv_pos r ⟨2, 1⟩ (by decide)]
        norm_num [QPair.toRat]
      have hsum : (qAdd (qMul r r) (qMul x x)).toRat =
          r.toRat * r.toRat + x.toRat * x.toRat := by
        rw [toRat_qAdd _ _ (qValid_qMul hr hr) (qValid_qMul hx hx),
          toRat_qMul, toRat_qMul]
      have hdiv : (qDiv x r).toRat = x.toRat / r.toRat :=
        toRat_qDiv_pos x r hrpos
      simp only [pointExpr, Expr.denote, Term.eval, F]
      rw [hhalf, hsum, hdiv]
      push_cast
      ring_nf

theorem prepareTrace_parts {steps : List Step} {p : Prepared}
    (hp : prepareTrace steps = some p) :
    KernelReflectionSelf.Domain.checkTrace (point qZero) steps = true ∧
      reifyTrace steps = some p.exprEnv ∧ p.stepsRev = steps.reverse := by
  cases hc : KernelReflectionSelf.Domain.checkTrace (point qZero) steps with
  | false => simp [prepareTrace, hc] at hp
  | true =>
      cases hr : reifyTrace steps with
      | none => simp [prepareTrace, hc, hr] at hp
      | some env =>
          simp [prepareTrace, hc, hr] at hp
          cases hp
          simp

theorem checkExprPoint_sound {steps : List Step} {p : Prepared}
    {e : Expr} {node : ℕ} {bound : I}
    (hp : prepareTrace steps = some p)
    (hc : checkExprPoint p e node bound = true) :
    bound.toBounds.Contains (e.denote 0) := by
  obtain ⟨hcheck, hreify, hrev⟩ := prepareTrace_parts hp
  have hzero : (point qZero).toBounds.Contains (0 : ℝ) := by
    simpa [qZero_toRat] using! contains_rat_point qZero
  cases hobs : lookup p.stepsRev node with
  | none => simp [checkExprPoint, hobs] at hc
  | some observed =>
      have hpairs : (lookupExpr p.exprEnv node == some e) = true ∧
          encloses bound observed = true := by
        simpa [checkExprPoint, hobs, Bool.and_eq_true] using! hc
      have hexpr : lookupExpr p.exprEnv node = some e := by
        simpa using! hpairs.1
      have hlookup : lookup steps.reverse node = some observed := by
        simpa only [← hrev] using! hobs
      have hvalue : observed.toBounds.Contains (e.denote 0) :=
        (checkedExpr_sound hzero hcheck hreify hexpr hlookup).2
      exact contains_of_encloses hvalue hpairs.2

theorem checkPoint_sound {steps : List Step} {p : Prepared}
    {t : Term} {x : QPair} {node : ℕ} {bound : I}
    (hp : prepareTrace steps = some p)
    (hc : checkPoint p t x node bound = true) :
    bound.toBounds.Contains ((pointExpr t x).denote 0) := by
  simp only [checkPoint, Bool.and_eq_true] at hc
  exact checkExprPoint_sound hp hc.2

theorem checkExprPoint_valid {p : Prepared} {e : Expr} {node : ℕ} {bound : I}
    (hc : checkExprPoint p e node bound = true) : validI bound = true := by
  cases hobs : lookup p.stepsRev node with
  | none => simp [checkExprPoint, hobs] at hc
  | some observed =>
      have hpairs : (lookupExpr p.exprEnv node == some e) = true ∧
          encloses bound observed = true := by
        simpa [checkExprPoint, hobs, Bool.and_eq_true] using! hc
      exact (encloses_parts hpairs.2).1

theorem checkPoint_valid {p : Prepared} {t : Term} {x : QPair}
    {node : ℕ} {bound : I}
    (hc : checkPoint p t x node bound = true) : validI bound = true := by
  simp only [checkPoint, Bool.and_eq_true] at hc
  exact checkExprPoint_valid hc.2

theorem checkPoint_eval_sound {steps : List Step} {p : Prepared}
    {t : Term} {x : QPair} {node : ℕ} {bound : I}
    (hp : prepareTrace steps = some p)
    (ht : validTerm t = true)
    (hc : checkPoint p t x node bound = true) :
    validI bound = true ∧ bound.toBounds.Contains (t.eval (x.toRat : ℝ)) := by
  have hx : qValid x = true := by
    have hpairs : qValid x = true ∧
        checkExprPoint p (pointExpr t x) node bound = true := by
      simpa only [checkPoint, Bool.and_eq_true] using! hc
    exact hpairs.1
  have hb := checkPoint_sound hp hc
  rw [pointExpr_denote_eq_eval t x ht hx] at hb
  exact ⟨checkPoint_valid hc, hb⟩

#print axioms checkExprPoint_sound
#print axioms checkPoint_sound
#print axioms qAbs_toRat
#print axioms argument_toRat
#print axioms pointExpr_denote_eq_eval
#print axioms checkPoint_eval_sound

end
end Li2Unified.Proofs.Potential.CompactAffine

end


end
