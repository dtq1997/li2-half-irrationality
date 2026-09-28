module
public import Li2Unified.Modular.Positive.Packed.P164
public import Li2Unified.Modular.Positive.Packed.P168
public import Li2Unified.Modular.Positive.Packed.P170
public import Li2Unified.Modular.Positive.Packed.P171
public import Li2Unified.Modular.Positive.Packed.P110

set_option backward.privateInPublic true

@[expose] public section

section
/-! Semantic and list-induction layer for the integer-pair reflection checker. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section
open Li2Unified.ParameterFamily

theorem lookupStep_mem_id {env : List Step} {id : ℕ} {s : Step}
    (h : lookupStep env id = some s) : s ∈ env ∧ s.id = id := by
  have hm : s ∈ env := List.mem_of_find?_eq_some (by simpa only [lookupStep] using h)
  have hid : (s.id == id) = true :=
    List.find?_some (p := fun entry : Step => entry.id == id)
      (by simpa only [lookupStep] using h)
  exact ⟨hm, by simpa using hid⟩

theorem lookupStep_good {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id : ℕ} {s : Step}
    (h : lookupStep env id = some s) :
    validI s.out = true ∧ s.out.toBounds.Contains (v id) ∧
      v id = evalOp x v s.op := by
  obtain ⟨hm, hid⟩ := lookupStep_mem_id h
  simpa only [hid, StepSem] using henv s hm

theorem lookup_good {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id : ℕ} {a : I}
    (h : lookup env id = some a) :
    validI a = true ∧ a.toBounds.Contains (v id) := by
  unfold lookup at h
  cases hs : lookupStep env id with
  | none => simp [hs] at h
  | some s =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst a
      exact ⟨(lookupStep_good henv hs).1, (lookupStep_good henv hs).2.1⟩

theorem logArgument_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id : ℕ} {q : QPair}
    (h : logArgument? env id = some q) :
    v id = Real.log (q.toRat : ℝ) := by
  unfold logArgument? at h
  cases hs : lookupStep env id with
  | none => simp [hs] at h
  | some s =>
      have hsem := (lookupStep_good henv hs).2.2
      rcases s with ⟨sid, op, out⟩
      cases op <;> simp [hs] at h
      case logAtom q' u rho k =>
        cases h
        simpa only [evalOp] using hsem

theorem atanArgument_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id : ℕ} {q : QPair}
    (h : atanArgument? env id = some q) :
    v id = Real.arctan (q.toRat : ℝ) := by
  unfold atanArgument? at h
  cases hs : lookupStep env id with
  | none => simp [hs] at h
  | some s =>
      have hsem := (lookupStep_good henv hs).2.2
      rcases s with ⟨sid, op, out⟩
      cases op <;> simp [hs] at h
      case atanSmall q' k =>
        cases h
        simpa only [evalOp] using hsem
      case atanHalf q' r k =>
        cases h
        simpa only [evalOp] using hsem
      case atanInverse q' r j =>
        cases h
        simpa only [evalOp] using hsem
      case «alias» j =>
        have halias : v id = v j := by simpa only [evalOp] using hsem
        cases ht : lookupStep env j with
        | none => simp [ht] at h
        | some t =>
            have hsem' := (lookupStep_good henv ht).2.2
            rcases t with ⟨tid, op', out'⟩
            cases op' <;> simp [ht] at h
            case atanSmall q' k =>
              cases h
              exact halias.trans (by simpa only [evalOp] using hsem')
            case atanHalf q' r k =>
              cases h
              exact halias.trans (by simpa only [evalOp] using hsem')
            case atanInverse q' r k =>
              cases h
              exact halias.trans (by simpa only [evalOp] using hsem')

theorem hPositive_witness_sem {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {a witness logId : ℕ} {w logStep : Step}
    {lo hi : ℕ}
    (hw : lookupStep env witness = some w)
    (hwmul : w.op = .mul a logId)
    (hlog : lookupStep env logId = some logStep)
    (hlogop : logStep.op = .log a lo hi) :
    v witness = v a * Real.log (v a) := by
  have hwsem := (lookupStep_good henv hw).2.2
  have hlsem := (lookupStep_good henv hlog).2.2
  rw [hwmul] at hwsem
  rw [hlogop] at hlsem
  simp only [evalOp] at hwsem hlsem
  rw [hlsem] at hwsem
  exact hwsem

theorem hPositive_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a witness : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .hPositiveProduct a witness, out⟩)
    (hcheck : checkStep env ⟨id, .hPositiveProduct a witness, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hw : lookupStep env witness with
      | none => simp [ha, hw] at hbody
      | some w =>
          simp only [ha, hw, Bool.and_eq_true] at hbody
          obtain ⟨⟨hzero, hc⟩, hshape⟩ := hbody
          cases hwmul : w.op with
          | mul left logId =>
              simp only [hwmul, Bool.and_eq_true] at hshape
              obtain ⟨hleft, hlogshape⟩ := hshape
              have hleft' : left = a := by simpa using hleft
              subst left
              cases hlog : lookupStep env logId with
              | none => simp [hlog] at hlogshape
              | some logStep =>
                  cases hlogop : logStep.op with
                  | log arg lo hi =>
                      simp [hlog, hlogop] at hlogshape
                      have harg : arg = a := by simpa using hlogshape
                      subst arg
                      have ha' := lookup_good henv ha
                      have hw' := (lookupStep_good henv hw).2.1
                      have hprod := hPositive_witness_sem henv hw hwmul hlog hlogop
                      have hwprod : w.out.toBounds.Contains
                          (v a * Real.log (v a)) := by
                        rw [← hprod]
                        exact hw'
                      have hb := h_positive_from_product_bound
                        ha'.1 hzero ha'.2 hwprod hc
                      have hv : validI out = true := (encloses_parts hc).1
                      change v id = mulLogAbs (v a) at hsem
                      exact ⟨hv, hsem ▸ hb⟩
                  | _ => simp [hlog, hlogop] at hlogshape
          | _ => simp [hwmul] at hshape

theorem log_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a lo hi : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .log a lo hi, out⟩)
    (hcheck : checkStep env ⟨id, .log a lo hi, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hlo : lookup env lo with
      | none => simp [ha, hlo] at hbody
      | some ilo =>
          cases hhi : lookup env hi with
          | none => simp [ha, hlo, hhi] at hbody
          | some ihi =>
              simp only [ha, hlo, hhi, Bool.and_eq_true] at hbody
              obtain ⟨⟨⟨hpos, hlarg⟩, huarg⟩, hc⟩ := hbody
              have hai := lookup_good henv ha
              have hli := lookup_good henv hlo
              have hui := lookup_good henv hhi
              have hloglo := logArgument_sound henv (by simpa using hlarg)
              have hloghi := logArgument_sound henv (by simpa using huarg)
              have hlbound : ilo.toBounds.Contains
                  (Real.log (ia.lo.toRat : ℝ)) := by
                rw [← hloglo]
                exact hli.2
              have hubound : ihi.toBounds.Contains
                  (Real.log (ia.hi.toRat : ℝ)) := by
                rw [← hloghi]
                exact hui.2
              have hb := log_sound hai.1 hpos hai.2 hlbound hubound hc
              have hv : validI out = true := (encloses_parts hc).1
              change v id = Real.log (v a) at hsem
              exact ⟨hv, hsem ▸ hb⟩

theorem atan_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a lo hi : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .atan a lo hi, out⟩)
    (hcheck : checkStep env ⟨id, .atan a lo hi, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hlo : lookup env lo with
      | none => simp [ha, hlo] at hbody
      | some ilo =>
          cases hhi : lookup env hi with
          | none => simp [ha, hlo, hhi] at hbody
          | some ihi =>
              simp only [ha, hlo, hhi, Bool.and_eq_true] at hbody
              obtain ⟨⟨hlarg, huarg⟩, hc⟩ := hbody
              have hai := lookup_good henv ha
              have hli := lookup_good henv hlo
              have hui := lookup_good henv hhi
              have hatanlo := atanArgument_sound henv (by simpa using hlarg)
              have hatanhi := atanArgument_sound henv (by simpa using huarg)
              have hlbound : ilo.toBounds.Contains
                  (Real.arctan (ia.lo.toRat : ℝ)) := by
                rw [← hatanlo]
                exact hli.2
              have hubound : ihi.toBounds.Contains
                  (Real.arctan (ia.hi.toRat : ℝ)) := by
                rw [← hatanhi]
                exact hui.2
              have hb := atan_sound hai.2 hlbound hubound hc
              have hv : validI out = true := (encloses_parts hc).1
              change v id = Real.arctan (v a) at hsem
              exact ⟨hv, hsem ▸ hb⟩

theorem hQuarter_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a lo hi : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .hQuarter a lo hi, out⟩)
    (hcheck : checkStep env ⟨id, .hQuarter a lo hi, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hlo : lookup env lo with
      | none => simp [ha, hlo] at hbody
      | some ilo =>
          cases hhi : lookup env hi with
          | none => simp [ha, hlo, hhi] at hbody
          | some ihi =>
              simp only [ha, hlo, hhi, Bool.and_eq_true] at hbody
              obtain ⟨⟨⟨⟨hzero, hquarter⟩, hlarg⟩, huarg⟩, hc⟩ := hbody
              have hai := lookup_good henv ha
              have hli := lookup_good henv hlo
              have hui := lookup_good henv hhi
              have hloglo := logArgument_sound henv (by simpa using hlarg)
              have hloghi := logArgument_sound henv (by simpa using huarg)
              have hlbound : ilo.toBounds.Contains
                  (Real.log (ia.lo.toRat : ℝ)) := by
                rw [← hloglo]
                exact hli.2
              have hubound : ihi.toBounds.Contains
                  (Real.log (ia.hi.toRat : ℝ)) := by
                rw [← hloghi]
                exact hui.2
              have hb := h_quarter_sound hai.1 hzero hquarter hai.2
                hlbound hubound hc
              have hv : validI out = true := (encloses_parts hc).1
              change v id = mulLogAbs (v a) at hsem
              exact ⟨hv, hsem ▸ hb⟩

theorem hCross_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a logRadius : ℕ} {radius : QPair}
    {out : I}
    (hsem : StepSem x v ⟨id, .hCross a logRadius radius, out⟩)
    (hcheck : checkStep env ⟨id, .hCross a logRadius radius, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hradius : lookup env logRadius with
      | none => simp [ha, hradius] at hbody
      | some ilog =>
          simp only [ha, hradius, Bool.and_eq_true] at hbody
          obtain ⟨⟨⟨⟨⟨⟨hr, hzero⟩, hquarter⟩, hleft⟩, hright⟩,
            hlogarg⟩, hc⟩ := hbody
          have hai := lookup_good henv ha
          have hri := lookup_good henv hradius
          have hlog := logArgument_sound henv (by simpa using hlogarg)
          have hlbound : ilog.toBounds.Contains
              (Real.log (radius.toRat : ℝ)) := by
            rw [← hlog]
            exact hri.2
          have hb := h_cross_sound hai.1 hr hzero hquarter hleft hright
            hai.2 hlbound hc
          have hv : validI out = true := (encloses_parts hc).1
          change v id = mulLogAbs (v a) at hsem
          exact ⟨hv, hsem ▸ hb⟩

theorem alias_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .alias a, out⟩)
    (hcheck : checkStep env ⟨id, .alias a, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      simp only [ha] at hbody
      have hai := lookup_good henv ha
      have hb := contains_of_encloses hai.2 hbody
      have hv : validI out = true := (encloses_parts hbody).1
      change v id = v a at hsem
      exact ⟨hv, hsem ▸ hb⟩

theorem add_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a b : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .add a b, out⟩)
    (hcheck : checkStep env ⟨id, .add a b, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hb : lookup env b with
      | none => simp [ha, hb] at hbody
      | some ib =>
          simp only [ha, hb] at hbody
          have hai := lookup_good henv ha
          have hbi := lookup_good henv hb
          have hc := add_sound hai.1 hbi.1 hai.2 hbi.2 hbody
          have hv : validI out = true := (encloses_parts hbody).1
          change v id = v a + v b at hsem
          exact ⟨hv, hsem ▸ hc⟩

theorem neg_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .neg a, out⟩)
    (hcheck : checkStep env ⟨id, .neg a, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      simp only [ha] at hbody
      have hai := lookup_good henv ha
      have hb := neg_sound hai.2 hbody
      have hv : validI out = true := (encloses_parts hbody).1
      change v id = -v a at hsem
      exact ⟨hv, hsem ▸ hb⟩

theorem mul_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id a b : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .mul a b, out⟩)
    (hcheck : checkStep env ⟨id, .mul a b, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  cases ha : lookup env a with
  | none => simp [ha] at hbody
  | some ia =>
      cases hb : lookup env b with
      | none => simp [ha, hb] at hbody
      | some ib =>
          simp only [ha, hb] at hbody
          have hai := lookup_good henv ha
          have hbi := lookup_good henv hb
          have hc := mul_sound hai.1 hbi.1 hai.2 hbi.2 hbody
          have hv : validI out = true := (encloses_parts hbody).1
          change v id = v a * v b at hsem
          exact ⟨hv, hsem ▸ hc⟩

theorem logAtom_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    {id : ℕ} {q u rho : QPair} {k : ℤ} {out : I}
    (hsem : StepSem x v ⟨id, .logAtom q u rho k, out⟩)
    (hcheck : checkStep env ⟨id, .logAtom q u rho k, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨_, hbody⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hq, hu⟩, hrho⟩, hu0⟩, hu1⟩, hrho0⟩,
    hrho1⟩, heq⟩, hc⟩ := hbody
  have hb := contains_of_encloses
    (contains_logAtom hq hu hrho hu0 hu1 hrho0 hrho1 heq) hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = Real.log (q.toRat : ℝ) at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem rat_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    {id : ℕ} {q : QPair} {out : I}
    (hsem : StepSem x v ⟨id, .rat q, out⟩)
    (hcheck : checkStep env ⟨id, .rat q, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, ⟨_, hc⟩⟩ := hcheck
  have hp : (point q).toBounds.Contains (q.toRat : ℝ) := ⟨le_rfl, le_rfl⟩
  have hb := contains_of_encloses hp hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = (q.toRat : ℝ) at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem var_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (hx : (⟨⟨135, 2048⟩, ⟨9, 128⟩⟩ : I).toBounds.Contains x)
    {id : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .var, out⟩)
    (hcheck : checkStep env ⟨id, .var, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, hc⟩ := hcheck
  have hb := contains_of_encloses hx hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = x at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem logTwo_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    {id : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .logTwo, out⟩)
    (hcheck : checkStep env ⟨id, .logTwo, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, hc⟩ := hcheck
  have hp : logTwoBounds.toBounds.Contains (Real.log 2) := by
    rw [logTwoBounds_toBounds]
    exact ParameterFamily.contains_logTwo
  have hb := contains_of_encloses hp hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = Real.log 2 at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem pi_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    {id : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .pi, out⟩)
    (hcheck : checkStep env ⟨id, .pi, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, hc⟩ := hcheck
  have hp : piBounds.toBounds.Contains Real.pi := by
    rw [piBounds_toBounds]
    exact ParameterFamily.contains_pi
  have hb := contains_of_encloses hp hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = Real.pi at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem atanSmall_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    {id : ℕ} {q : QPair} {k : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .atanSmall q k, out⟩)
    (hcheck : checkStep env ⟨id, .atanSmall q k, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, ⟨⟨⟨hq, hq0⟩, hq1⟩, hc⟩⟩ := hcheck
  have hb := contains_of_encloses (contains_atanSmall hq hq0 hq1) hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = Real.arctan (q.toRat : ℝ) at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem atanHalf_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    {id : ℕ} {q r : QPair} {k : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .atanHalf q r k, out⟩)
    (hcheck : checkStep env ⟨id, .atanHalf q r k, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, ⟨⟨⟨⟨⟨hq, hr⟩, hr0⟩, hr1⟩, heq⟩, hc⟩⟩ := hcheck
  have hb := contains_of_encloses (contains_atanHalf hq hr hr0 hr1 heq) hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = Real.arctan (q.toRat : ℝ) at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem atanInverse_check_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (henv : EnvGood x v env) {id : ℕ} {q r : QPair} {j : ℕ}
    {out : I}
    (hsem : StepSem x v ⟨id, .atanInverse q r j, out⟩)
    (hcheck : checkStep env ⟨id, .atanInverse q r j, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, hbody⟩ := hcheck
  obtain ⟨⟨⟨⟨hq, hr⟩, hq0⟩, heq⟩, hmatch⟩ := hbody
  cases hj : lookupStep env j with
  | none => simp [hj] at hmatch
  | some inv =>
      simp only [hj, Bool.and_eq_true] at hmatch
      obtain ⟨harg, hc⟩ := hmatch
      have hargsem := atanArgument_sound henv (by simpa using harg)
      have hinv := lookupStep_good henv hj
      have har : inv.out.toBounds.Contains (Real.arctan (r.toRat : ℝ)) := by
        rw [← hargsem]
        exact hinv.2.1
      have hb := contains_of_encloses
        (contains_atanInverse hq hr hq0 heq hinv.1 har) hc
      have hv : validI out = true := (encloses_parts hc).1
      change v id = Real.arctan (q.toRat : ℝ) at hsem
      exact ⟨hv, hsem ▸ hb⟩

theorem envGood_cons {x : ℝ} {v : ℕ → ℝ} {env : List Step} {s : Step}
    (henv : EnvGood x v env)
    (hvalid : validI s.out = true)
    (hbound : s.out.toBounds.Contains (v s.id))
    (hsem : StepSem x v s) : EnvGood x v (s :: env) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨hvalid, hbound, hsem⟩
  · exact henv t ht

theorem checkGo_sound_of_step_sound {x : ℝ} {v : ℕ → ℝ}
    (hstep : ∀ env s, EnvGood x v env → StepSem x v s →
      checkStep env s = true →
      validI s.out = true ∧ s.out.toBounds.Contains (v s.id)) :
    ∀ env ss, EnvGood x v env →
      (∀ s ∈ ss, StepSem x v s) →
      checkGo env ss = true →
      EnvGood x v (ss.reverse ++ env) := by
  intro env ss
  induction ss generalizing env with
  | nil =>
      intro henv _ _
      simpa using henv
  | cons s ss ih =>
      intro henv hsem hcheck
      have hpair : checkStep env s = true ∧ checkGo (s :: env) ss = true := by
        simpa only [checkGo, Bool.and_eq_true] using hcheck
      have hs : StepSem x v s := hsem s (by simp)
      obtain ⟨hvalid, hbound⟩ := hstep env s henv hs hpair.1
      have henv' : EnvGood x v (s :: env) :=
        envGood_cons henv hvalid hbound hs
      have hsem' : ∀ t ∈ ss, StepSem x v t := by
        intro t ht
        exact hsem t (by simp [ht])
      have htail := ih (s :: env) henv' hsem' hpair.2
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using htail

theorem checkStep_sound {x : ℝ} {v : ℕ → ℝ} {env : List Step}
    (hx : (⟨⟨135, 2048⟩, ⟨9, 128⟩⟩ : I).toBounds.Contains x)
    (henv : EnvGood x v env) {s : Step}
    (hsem : StepSem x v s) (hcheck : checkStep env s = true) :
    validI s.out = true ∧ s.out.toBounds.Contains (v s.id) := by
  rcases s with ⟨id, op, out⟩
  cases op with
  | rat q => exact rat_check_sound hsem hcheck
  | var => exact var_check_sound hx hsem hcheck
  | logTwo => exact logTwo_check_sound hsem hcheck
  | pi => exact pi_check_sound hsem hcheck
  | logAtom q u rho k => exact logAtom_check_sound hsem hcheck
  | atanSmall q k => exact atanSmall_check_sound hsem hcheck
  | atanHalf q r k => exact atanHalf_check_sound hsem hcheck
  | atanInverse q r j => exact atanInverse_check_sound henv hsem hcheck
  | «alias» a => exact alias_check_sound henv hsem hcheck
  | add a b => exact add_check_sound henv hsem hcheck
  | neg a => exact neg_check_sound henv hsem hcheck
  | mul a b => exact mul_check_sound henv hsem hcheck
  | log a lo hi => exact log_check_sound henv hsem hcheck
  | atan a lo hi => exact atan_check_sound henv hsem hcheck
  | hPositiveProduct a witness => exact hPositive_check_sound henv hsem hcheck
  | hQuarter a lo hi => exact hQuarter_check_sound henv hsem hcheck
  | hCross a logRadius radius => exact hCross_check_sound henv hsem hcheck

theorem checkTrace_sound {x : ℝ} {v : ℕ → ℝ} {steps : List Step}
    (hx : (⟨⟨135, 2048⟩, ⟨9, 128⟩⟩ : I).toBounds.Contains x)
    (hsem : ∀ s ∈ steps, StepSem x v s)
    (hcheck : checkTrace steps = true) :
    EnvGood x v steps.reverse := by
  have hnil : EnvGood x v [] := by
    intro s hs
    cases hs
  have hstep : ∀ env s, EnvGood x v env → StepSem x v s →
      checkStep env s = true →
      validI s.out = true ∧ s.out.toBounds.Contains (v s.id) := by
    intro env s henv hs hc
    exact checkStep_sound hx henv hs hc
  simpa only [checkTrace, List.append_nil] using
    (checkGo_sound_of_step_sound hstep [] steps hnil hsem hcheck)

theorem checkTrace_lookup_sound {x : ℝ} {v : ℕ → ℝ}
    {steps : List Step} {id : ℕ} {out : I}
    (hx : (⟨⟨135, 2048⟩, ⟨9, 128⟩⟩ : I).toBounds.Contains x)
    (hsem : ∀ s ∈ steps, StepSem x v s)
    (hcheck : checkTrace steps = true)
    (hlookup : lookup steps.reverse id = some out) :
    validI out = true ∧ out.toBounds.Contains (v id) :=
  lookup_good (checkTrace_sound hx hsem hcheck) hlookup

end
end Li2Unified.Proofs.Potential.KernelReflectionSelf

#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.checkGo_sound_of_step_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.checkTrace_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.checkTrace_lookup_sound

end

section
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain
noncomputable section

open Li2Unified.Proofs.Potential.KernelReflectionSelf

private theorem checkStep_old_of_ne_var (domain : I) (env : List Step)
    (s : Step) (h : s.op ≠ .var)
    (hc : checkStep domain env s = true) :
    KernelReflectionSelf.checkStep env s = true := by
  rcases s with ⟨id, op, out⟩
  cases op <;> try (exact hc)
  case var => exact (h rfl).elim

private theorem var_check_sound {x : ℝ} {v : ℕ → ℝ} {domain : I}
    {env : List Step} (hx : domain.toBounds.Contains x)
    {id : ℕ} {out : I}
    (hsem : StepSem x v ⟨id, .var, out⟩)
    (hcheck : checkStep domain env ⟨id, .var, out⟩ = true) :
    validI out = true ∧ out.toBounds.Contains (v id) := by
  simp only [checkStep, Bool.and_eq_true] at hcheck
  obtain ⟨_, hc⟩ := hcheck
  have hb := contains_of_encloses hx hc
  have hv : validI out = true := (encloses_parts hc).1
  change v id = x at hsem
  exact ⟨hv, hsem ▸ hb⟩

theorem checkStep_sound {x : ℝ} {v : ℕ → ℝ} {domain : I}
    {env : List Step} (hx : domain.toBounds.Contains x)
    (henv : EnvGood x v env) {s : Step}
    (hsem : StepSem x v s)
    (hcheck : checkStep domain env s = true) :
    validI s.out = true ∧ s.out.toBounds.Contains (v s.id) := by
  rcases s with ⟨id, op, out⟩
  cases op with
  | var => exact var_check_sound hx hsem hcheck
  | rat q => exact KernelReflectionSelf.rat_check_sound hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | logTwo => exact KernelReflectionSelf.logTwo_check_sound hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | pi => exact KernelReflectionSelf.pi_check_sound hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | logAtom q u rho k => exact KernelReflectionSelf.logAtom_check_sound hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | atanSmall q k => exact KernelReflectionSelf.atanSmall_check_sound hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | atanHalf q r k => exact KernelReflectionSelf.atanHalf_check_sound hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | atanInverse q r j => exact KernelReflectionSelf.atanInverse_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | «alias» a => exact KernelReflectionSelf.alias_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | add a b => exact KernelReflectionSelf.add_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | neg a => exact KernelReflectionSelf.neg_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | mul a b => exact KernelReflectionSelf.mul_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | log a lo hi => exact KernelReflectionSelf.log_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | atan a lo hi => exact KernelReflectionSelf.atan_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | hPositiveProduct a witness => exact KernelReflectionSelf.hPositive_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | hQuarter a lo hi => exact KernelReflectionSelf.hQuarter_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)
  | hCross a logRadius radius => exact KernelReflectionSelf.hCross_check_sound henv hsem (checkStep_old_of_ne_var domain env _ (by simp) hcheck)

theorem checkGo_sound_of_step_sound {x : ℝ} {v : ℕ → ℝ} {domain : I}
    (hstep : ∀ env s, EnvGood x v env → StepSem x v s →
      checkStep domain env s = true →
      validI s.out = true ∧ s.out.toBounds.Contains (v s.id)) :
    ∀ env ss, EnvGood x v env →
      (∀ s ∈ ss, StepSem x v s) →
      checkGo domain env ss = true →
      EnvGood x v (ss.reverse ++ env) := by
  intro env ss
  induction ss generalizing env with
  | nil =>
      intro henv _ _
      simpa using henv
  | cons s ss ih =>
      intro henv hsem hcheck
      have hpair : checkStep domain env s = true ∧
          checkGo domain (s :: env) ss = true := by
        simpa only [checkGo, Bool.and_eq_true] using hcheck
      have hs : StepSem x v s := hsem s (by simp)
      obtain ⟨hvalid, hbound⟩ := hstep env s henv hs hpair.1
      have henv' : EnvGood x v (s :: env) :=
        KernelReflectionSelf.envGood_cons henv hvalid hbound hs
      have hsem' : ∀ t ∈ ss, StepSem x v t := by
        intro t ht
        exact hsem t (by simp [ht])
      have htail := ih (s :: env) henv' hsem' hpair.2
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using htail

theorem checkTrace_sound {x : ℝ} {v : ℕ → ℝ} {domain : I}
    {steps : List Step} (hx : domain.toBounds.Contains x)
    (hsem : ∀ s ∈ steps, StepSem x v s)
    (hcheck : checkTrace domain steps = true) :
    EnvGood x v steps.reverse := by
  have hnil : EnvGood x v [] := by
    intro s hs
    cases hs
  have hstep : ∀ env s, EnvGood x v env → StepSem x v s →
      checkStep domain env s = true →
      validI s.out = true ∧ s.out.toBounds.Contains (v s.id) := by
    intro env s henv hs hc
    exact checkStep_sound hx henv hs hc
  simpa only [checkTrace, List.append_nil] using
    (checkGo_sound_of_step_sound hstep [] steps hnil hsem hcheck)

theorem checkTrace_lookup_sound {x : ℝ} {v : ℕ → ℝ} {domain : I}
    {steps : List Step} {id : ℕ} {out : I}
    (hx : domain.toBounds.Contains x)
    (hsem : ∀ s ∈ steps, StepSem x v s)
    (hcheck : checkTrace domain steps = true)
    (hlookup : lookup steps.reverse id = some out) :
    validI out = true ∧ out.toBounds.Contains (v id) :=
  KernelReflectionSelf.lookup_good (checkTrace_sound hx hsem hcheck) hlookup

end
end Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain

#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain.checkTrace_sound
#print axioms Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain.checkTrace_lookup_sound

end


end
