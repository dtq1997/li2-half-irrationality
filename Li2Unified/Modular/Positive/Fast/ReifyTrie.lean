module
public import Li2Unified.Modular.Positive.Fast.TraceTrie
public import Li2Unified.Modular.Positive.Packed.P206

set_option backward.privateInPublic true

/-!
# Trie-backed reification

`reifyTrace` and the certificate checkers look entries up in association lists, so one
certificate costs quadratically many kernel reduction steps. Here the same entries sit in
the binary trie of `TraceTrie`, and the checkers take their two lookups as arguments. Each
fast checker is proved to imply the original one.
-/

@[expose] public section
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain (Trie trieLook)
open Li2Unified.Proofs.Potential.ReflectionProgram

def reifyOpWith (look : Nat → Option Expr) : Op → Option Expr
  | .rat q => some (.rat q)
  | .var => some .var
  | .logTwo => some .logTwo
  | .pi => some .pi
  | .logAtom q _ _ _ => some (.log (.rat q))
  | .atanSmall q _ => some (.atan (.rat q))
  | .atanHalf q _ _ => some (.atan (.rat q))
  | .atanInverse q _ _ => some (.atan (.rat q))
  | .alias a => look a
  | .add a b => do
      let ea ← look a
      let eb ← look b
      return .add ea eb
  | .neg a => (look a).map Expr.neg
  | .mul a b => do
      let ea ← look a
      let eb ← look b
      return .mul ea eb
  | .log a _ _ => (look a).map Expr.log
  | .atan a _ _ => (look a).map Expr.atan
  | .hPositiveProduct a _ => (look a).map Expr.H
  | .hQuarter a _ _ => (look a).map Expr.H
  | .hCross a _ _ => (look a).map Expr.H

theorem reifyOp_eq_with (env : ExprEnv) (op : Op) :
    reifyOp env op = reifyOpWith (lookupExpr env) op := by
  cases op <;> rfl

def trieExpr (d : Nat) (t : Trie (Step × Expr)) (k : Nat) : Option Expr :=
  (trieLook d t k).map Prod.snd

def trieOut (d : Nat) (t : Trie (Step × Expr)) (k : Nat) : Option I :=
  (trieLook d t k).map (fun p => p.1.out)

def reifyFast (d : Nat) (t : Trie (Step × Expr)) : List Step → Option (Trie (Step × Expr))
  | [] => some t
  | s :: ss =>
      if s.id < 2 ^ d then
        match trieExpr d t s.id, reifyOpWith (trieExpr d t) s.op with
        | none, some e => reifyFast d (t.insert d s.id (s, e)) ss
        | _, _ => none
      else none

/-- The trie represents `env` exactly, and every id in `env` is below `2^d`. -/
def RepE (d : Nat) (t : Trie (Step × Expr)) (env : ExprEnv) : Prop :=
  (∀ k, k < 2 ^ d → t.find d k = env.find? (fun p => p.1.id == k)) ∧
    ∀ p ∈ env, p.1.id < 2 ^ d

theorem repE_nil (d : Nat) : RepE d .nil [] :=
  ⟨fun k _ => by simp [Trie.find_nil], fun _ h => by simp at h⟩

theorem trieLook_eq_find {d : Nat} {t : Trie (Step × Expr)} {env : ExprEnv}
    (h : RepE d t env) (k : Nat) :
    trieLook d t k = env.find? (fun p => p.1.id == k) := by
  unfold trieLook
  split
  · exact h.1 k ‹_›
  · symm
    rw [List.find?_eq_none]
    intro p hp
    have := h.2 p hp
    simp only [beq_iff_eq]
    omega

theorem trieExpr_eq {d : Nat} {t : Trie (Step × Expr)} {env : ExprEnv}
    (h : RepE d t env) : trieExpr d t = lookupExpr env := by
  funext k
  simp only [trieExpr, lookupExpr, trieLook_eq_find h]

theorem trieOut_eq {d : Nat} {t : Trie (Step × Expr)} {env : ExprEnv} {steps : List Step}
    (h : RepE d t env) (hs : env.map Prod.fst = steps) : trieOut d t = lookup steps := by
  funext k
  subst hs
  simp [trieOut, lookup, lookupStep, trieLook_eq_find h, List.find?_map, Function.comp_def]

theorem repE_insert {d : Nat} {t : Trie (Step × Expr)} {env : ExprEnv} {s : Step} {e : Expr}
    (h : RepE d t env) (hs : s.id < 2 ^ d) :
    RepE d (t.insert d s.id (s, e)) ((s, e) :: env) := by
  refine ⟨fun k hk => ?_, fun p hp => ?_⟩
  · rw [Trie.find_insert d t s.id k (s, e) hs hk, h.1 k hk]
    simp only [List.find?_cons]
    by_cases hkk : k = s.id
    · subst hkk; simp
    · have : (s.id == k) = false := by simp; omega
      simp [hkk, this]
  · rcases List.mem_cons.mp hp with rfl | hp'
    · exact hs
    · exact h.2 p hp'

theorem reifyFast_sound (d : Nat) :
    ∀ (ss : List Step) (t : Trie (Step × Expr)) (env : ExprEnv) (t' : Trie (Step × Expr)),
      RepE d t env → reifyFast d t ss = some t' →
        ∃ env', reifyGo env ss = some env' ∧ RepE d t' env' ∧
          env'.map Prod.fst = ss.reverse ++ env.map Prod.fst
  | [], t, env, t', h, hr => by
      simp only [reifyFast, Option.some.injEq] at hr
      subst hr
      exact ⟨env, rfl, h, by simp⟩
  | s :: ss, t, env, t', h, hr => by
      unfold reifyFast at hr
      split at hr
      · rename_i hid
        rw [trieExpr_eq h, ← reifyOp_eq_with] at hr
        split at hr
        · rename_i e hnone hsome
          obtain ⟨env', h1, h2, h3⟩ :=
            reifyFast_sound d ss _ ((s, e) :: env) t' (repE_insert h hid) hr
          refine ⟨env', ?_, h2, by simp [h3]⟩
          simp only [reifyGo, hnone, hsome]
          exact h1
        · simp at hr
      · simp at hr

/-- A trace that passes the fast interval check and the fast reification is prepared,
and the two trie lookups agree with the lookups of the prepared trace. -/
theorem prepareTrace_of_fast {steps : List Step} {t : Trie (Step × Expr)}
    (htrace : Domain.fastCheckTrace 10 (point qZero) steps = true)
    (hr : reifyFast 10 .nil steps = some t) :
    ∃ p, prepareTrace steps = some p ∧
      trieExpr 10 t = lookupExpr p.exprEnv ∧ trieOut 10 t = lookup p.stepsRev := by
  obtain ⟨env, henv, hrep, hfst⟩ := reifyFast_sound 10 steps .nil [] t (repE_nil 10) hr
  refine ⟨⟨steps.reverse, env⟩, ?_, trieExpr_eq hrep, trieOut_eq hrep (by simpa using hfst)⟩
  simp [prepareTrace, Domain.fastCheckTrace_sound htrace, reifyTrace, henv]

/-! ### Checkers with the lookups as arguments -/

def checkExprPointWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (e : Expr) (node : Nat) (bound : I) : Bool :=
  (lookE node == some e) &&
  match lookO node with
  | some observed => encloses bound observed
  | none => false

def checkPointWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (t : Term) (x : QPair) (node : Nat) (bound : I) : Bool :=
  qValid x &&
  checkExprPointWith lookE lookO (pointExpr t x) node bound

def checkChordWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (t : Term) (a b alpha beta : QPair)
    (leftNode : Nat) (leftBound : I)
    (rightNode : Nat) (rightBound : I) : Bool :=
  convexGuard t a b && qValid alpha && qValid beta &&
  checkPointWith lookE lookO t a leftNode leftBound &&
  checkPointWith lookE lookO t b rightNode rightBound &&
  qLE leftBound.hi (affineAt a b alpha beta a) &&
  qLE rightBound.hi (affineAt a b alpha beta b)

def checkTangentWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (t : Term) (a b alpha beta : QPair)
    (midNode : Nat) (midBound : I)
    (derivativeNode : Nat) (derivativeBound : I) : Bool :=
  let m := midpoint a b
  let deviation := qMax (qAbs (qSub derivativeBound.lo beta))
                        (qAbs (qSub derivativeBound.hi beta))
  concaveGuard t a b && qValid alpha && qValid beta &&
  checkPointWith lookE lookO t m midNode midBound &&
  derivativeValid t m &&
  checkExprPointWith lookE lookO (derivativeExpr t m) derivativeNode derivativeBound &&
  qLE (qAdd midBound.hi (qMul deviation (radius a b))) alpha

def checkPartWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (t : Term) (a b : QPair) (part : PartCert) : Bool :=
  match part.witness with
  | .chord ln li rn ri => checkChordWith lookE lookO t a b part.alpha part.beta ln li rn ri
  | .tangent mn mi dn di => checkTangentWith lookE lookO t a b part.alpha part.beta mn mi dn di
  | .cross outer u rho k => checkCross t a b part.alpha part.beta outer u rho k

def checkPartsWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (a b : QPair) : List Term → List PartCert → Bool
  | [], [] => true
  | t :: ts, c :: cs => checkPartWith lookE lookO t a b c && checkPartsWith lookE lookO a b ts cs
  | _, _ => false

def checkBoxWith (lookE : Nat → Option Expr) (lookO : Nat → Option I)
    (terms : List Term) (box : BoxCert) : Bool :=
  qValid box.left && qValid box.right && qLT box.left box.right &&
  qValid box.alpha && qValid box.beta &&
  checkPartsWith lookE lookO box.left box.right terms box.parts &&
  qEq box.alpha (box.parts.foldl (fun acc part => qAdd acc part.alpha) qZero) &&
  qEq box.beta (box.parts.foldl (fun acc part => qAdd acc part.beta) qZero)

theorem checkExprPoint_eq_with (p : Prepared) (e : Expr) (node : Nat) (bound : I) :
    checkExprPoint p e node bound =
      checkExprPointWith (lookupExpr p.exprEnv) (lookup p.stepsRev) e node bound := rfl

theorem checkParts_eq_with (p : Prepared) (a b : QPair) :
    ∀ (ts : List Term) (cs : List PartCert), checkParts p a b ts cs =
      checkPartsWith (lookupExpr p.exprEnv) (lookup p.stepsRev) a b ts cs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, c :: cs => by
      simp only [checkParts, checkPartsWith, checkParts_eq_with p a b ts cs]
      rfl

theorem checkBox_eq_with (p : Prepared) (terms : List Term) (box : BoxCert) :
    checkBox p terms box =
      checkBoxWith (lookupExpr p.exprEnv) (lookup p.stepsRev) terms box := by
  simp only [checkBox, checkBoxWith, checkParts_eq_with]

end Li2Unified.Proofs.Potential.CompactAffine

end
