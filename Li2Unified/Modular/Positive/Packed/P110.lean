module
public import Init

set_option backward.privateInPublic true

@[expose] public section

section
/-! Pure integer-pair checker for the ray-007 reflection pilot.
The denominator is checked, not normalized. Each step reads stored predecessor
bounds, so multiplication does not recursively expand the whole trace. -/
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf

structure QPair where
  num : Int
  den : Nat
  deriving Repr, DecidableEq

structure I where
  lo : QPair
  hi : QPair
  deriving Repr, DecidableEq

def qZero : QPair := ⟨0, 1⟩
def qOne : QPair := ⟨1, 1⟩
def qQuarter : QPair := ⟨1, 4⟩
def qHalf : QPair := ⟨1, 2⟩

def qValid (q : QPair) : Bool := decide (0 < q.den)
def qLE (a b : QPair) : Bool :=
  decide (a.num * Int.ofNat b.den ≤ b.num * Int.ofNat a.den)
def qLT (a b : QPair) : Bool :=
  decide (a.num * Int.ofNat b.den < b.num * Int.ofNat a.den)
def qEq (a b : QPair) : Bool := qLE a b && qLE b a

def qAdd (a b : QPair) : QPair :=
  ⟨a.num * Int.ofNat b.den + b.num * Int.ofNat a.den, a.den * b.den⟩
def qNeg (a : QPair) : QPair := ⟨-a.num, a.den⟩
def qMul (a b : QPair) : QPair := ⟨a.num * b.num, a.den * b.den⟩
def qInv (a : QPair) : QPair :=
  if 0 < a.num then ⟨Int.ofNat a.den, a.num.toNat⟩
  else if a.num < 0 then ⟨-(Int.ofNat a.den), (-a.num).toNat⟩
  else ⟨0, 0⟩
def qDiv (a b : QPair) : QPair := qMul a (qInv b)
def qSub (a b : QPair) : QPair := qAdd a (qNeg b)
def qPow (a : QPair) : Nat → QPair
  | 0 => qOne
  | n + 1 => qMul (qPow a n) a
def qPow2Z (k : Int) : QPair :=
  if 0 ≤ k then ⟨Int.ofNat (2 ^ k.toNat), 1⟩
  else ⟨1, 2 ^ (-k).toNat⟩
def qMin (a b : QPair) : QPair := if qLE a b then a else b
def qMax (a b : QPair) : QPair := if qLE a b then b else a

def point (q : QPair) : I := ⟨q, q⟩
def add (a b : I) : I := ⟨qAdd a.lo b.lo, qAdd a.hi b.hi⟩
def neg (a : I) : I := ⟨qNeg a.hi, qNeg a.lo⟩
def mul (a b : I) : I :=
  ⟨qMin (qMin (qMul a.lo b.lo) (qMul a.lo b.hi))
        (qMin (qMul a.hi b.lo) (qMul a.hi b.hi)),
   qMax (qMax (qMul a.lo b.lo) (qMul a.lo b.hi))
        (qMax (qMul a.hi b.lo) (qMul a.hi b.hi))⟩

def validI (a : I) : Bool :=
  qValid a.lo && qValid a.hi && qLE a.lo a.hi
def encloses (out candidate : I) : Bool :=
  validI out && validI candidate &&
    qLE out.lo candidate.lo && qLE candidate.hi out.hi

def logTwoBounds : I :=
  ⟨⟨6931471803, 10000000000⟩, ⟨6931471808, 10000000000⟩⟩
def piBounds : I :=
  ⟨⟨3141592, 1000000⟩, ⟨3141593, 1000000⟩⟩

def logPartial (r : QPair) (n : Nat) : QPair :=
  (List.range n).foldl
    (fun acc i => qAdd acc (qDiv (qPow (qSub qOne r) (i + 1))
      ⟨Int.ofNat (i + 1), 1⟩)) qZero
def logError (r : QPair) (n : Nat) : QPair :=
  qDiv (qPow (qSub qOne r) (n + 1)) r
def reducedLogBounds (r : QPair) (n : Nat) : I :=
  let p := logPartial r n
  let e := logError r n
  ⟨qSub (qNeg p) e, qAdd (qNeg p) e⟩
def scaledLogBounds (k : Int) (u : QPair) : I :=
  add (mul (point ⟨k, 1⟩) logTwoBounds) (reducedLogBounds u 24)
def anchoredLogBounds (k : Int) (u rho : QPair) : I :=
  add (scaledLogBounds k u) (neg (reducedLogBounds rho 2))

def atanPartial (r : QPair) (n : Nat) : QPair :=
  (List.range n).foldl (fun acc i =>
    let term := qDiv (qPow r (2*i + 1)) ⟨Int.ofNat (2*i + 1), 1⟩
    qAdd acc (if i % 2 == 0 then term else qNeg term)) qZero
def smallAtanBounds (r : QPair) (k : Nat) : I :=
  ⟨atanPartial r (2*k), atanPartial r (2*k + 1)⟩
def halfAtanBounds (r : QPair) (k : Nat) : I :=
  add (smallAtanBounds qHalf k) (smallAtanBounds r k)
def inverseAtanBounds (a : I) : I :=
  add (mul (point qHalf) piBounds) (neg a)

/-- The constructors mirror exactly the operations in the typed trace. The
nonlinear constructors' rational side conditions are checked separately from
their imported real-analysis soundness lemmas. -/
inductive Op where
  | rat (q : QPair)
  | var
  | logTwo
  | pi
  | logAtom (q u rho : QPair) (k : Int)
  | atanSmall (q : QPair) (terms : Nat)
  | atanHalf (q r : QPair) (terms : Nat)
  | atanInverse (q r : QPair) (inverseNode : Nat)
  | alias (a : Nat)
  | add (a b : Nat)
  | neg (a : Nat)
  | mul (a b : Nat)
  | log (a lo hi : Nat)
  | atan (a lo hi : Nat)
  | hPositiveProduct (a witness : Nat)
  | hQuarter (a lo hi : Nat)
  | hCross (a logRadius : Nat) (radius : QPair)
  deriving Repr

structure Step where
  id : Nat
  op : Op
  out : I
  deriving Repr

def lookupStep (env : List Step) (id : Nat) : Option Step :=
  env.find? (fun entry => entry.id == id)
def lookup (env : List Step) (id : Nat) : Option I :=
  (lookupStep env id).map Step.out

def logArgument? (env : List Step) (id : Nat) : Option QPair :=
  match lookupStep env id with
  | some ⟨_, .logAtom q _ _ _, _⟩ => some q
  | _ => none

def atanArgument? (env : List Step) (id : Nat) : Option QPair :=
  match lookupStep env id with
  | some ⟨_, .atanSmall q _, _⟩ => some q
  | some ⟨_, .atanHalf q _ _, _⟩ => some q
  | some ⟨_, .atanInverse q _ _, _⟩ => some q
  | some ⟨_, .alias j, _⟩ =>
      match lookupStep env j with
      | some ⟨_, .atanSmall q _, _⟩ => some q
      | some ⟨_, .atanHalf q _ _, _⟩ => some q
      | some ⟨_, .atanInverse q _ _, _⟩ => some q
      | _ => none
  | _ => none

def checkStep (env : List Step) (s : Step) : Bool :=
  let fresh := !(env.any (fun entry => entry.id == s.id))
  fresh && match s.op with
  | .rat q => qValid q && encloses s.out (point q)
  | .var => encloses s.out ⟨⟨135, 2048⟩, ⟨9, 128⟩⟩
  | .logTwo => encloses s.out logTwoBounds
  | .pi => encloses s.out piBounds
  | .logAtom q u rho k =>
      qValid q && qValid u && qValid rho &&
      qLT qZero u && qLE u qOne && qLT qZero rho && qLE rho qOne &&
      qEq q (qDiv (qMul (qPow2Z k) u) rho) &&
      encloses s.out (anchoredLogBounds k u rho)
  | .atanSmall q k =>
      qValid q && qLE qZero q && qLT q qOne &&
      encloses s.out (smallAtanBounds q k)
  | .atanHalf q r k =>
      qValid q && qValid r && qLE qZero r && qLE r qHalf &&
      qEq q (qDiv (qAdd qHalf r) (qSub qOne (qMul qHalf r))) &&
      encloses s.out (halfAtanBounds r k)
  | .atanInverse q r j =>
      qValid q && qValid r && qLT qZero q && qEq r (qInv q) &&
      match lookupStep env j with
      | some inv =>
          (atanArgument? env j == some r) && encloses s.out (inverseAtanBounds inv.out)
      | none => false
  | .alias a =>
      match lookup env a with
      | some ia => encloses s.out ia
      | none => false
  | .add a b =>
      match lookup env a, lookup env b with
      | some ia, some ib => encloses s.out (add ia ib)
      | _, _ => false
  | .neg a =>
      match lookup env a with
      | some ia => encloses s.out (neg ia)
      | none => false
  | .mul a b =>
      match lookup env a, lookup env b with
      | some ia, some ib => encloses s.out (mul ia ib)
      | _, _ => false
  | .log a lo hi =>
      match lookup env a, lookup env lo, lookup env hi with
      | some ia, some ilo, some ihi =>
          qLT qZero ia.lo &&
          (logArgument? env lo == some ia.lo) &&
          (logArgument? env hi == some ia.hi) &&
          encloses s.out ⟨ilo.lo, ihi.hi⟩
      | _, _, _ => false
  | .atan a lo hi =>
      match lookup env a, lookup env lo, lookup env hi with
      | some ia, some ilo, some ihi =>
          (atanArgument? env lo == some ia.lo) &&
          (atanArgument? env hi == some ia.hi) &&
          encloses s.out ⟨ilo.lo, ihi.hi⟩
      | _, _, _ => false
  | .hPositiveProduct a witness =>
      match lookup env a, lookupStep env witness with
      | some ia, some w =>
          qLE qZero ia.lo && encloses s.out w.out &&
          match w.op with
          | .mul left logId =>
              (left == a) &&
              match lookupStep env logId with
              | some logStep =>
                  match logStep.op with
                  | .log arg _ _ => arg == a
                  | _ => false
              | none => false
          | _ => false
      | _, _ => false
  | .hQuarter a lo hi =>
      match lookup env a, lookup env lo, lookup env hi with
      | some ia, some ilo, some ihi =>
          qLE qZero ia.lo && qLE ia.hi qQuarter &&
          (logArgument? env lo == some ia.lo) &&
          (logArgument? env hi == some ia.hi) &&
          encloses s.out ⟨qMul ia.hi ihi.lo, qMul ia.lo ilo.hi⟩
      | _, _, _ => false
  | .hCross a logRadius radius =>
      match lookup env a, lookup env logRadius with
      | some ia, some ilog =>
          qValid radius && qLE qZero radius && qLE radius qQuarter &&
          qLE (qNeg radius) ia.lo && qLE ia.hi radius &&
          (logArgument? env logRadius == some radius) &&
          encloses s.out ⟨qMul radius ilog.lo, qNeg (qMul radius ilog.lo)⟩
      | _, _ => false

def checkGo (env : List Step) : List Step → Bool
  | [] => true
  | s :: ss => checkStep env s && checkGo (s :: env) ss

def checkTrace (steps : List Step) : Bool := checkGo [] steps

end Li2Unified.Proofs.Potential.KernelReflectionSelf

end

section
/-! Fixed real-expression graph reified from a checked interval trace.
This layer only records syntax. It does not assert interval or real soundness. -/
namespace Li2Unified.Proofs.Potential.ReflectionProgram

open Li2Unified.Proofs.Potential.KernelReflectionSelf

inductive Expr where
  | rat (q : QPair)
  | var
  | logTwo
  | pi
  | add (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | log (a : Expr)
  | atan (a : Expr)
  | H (a : Expr)
  deriving Repr, DecidableEq

abbrev ExprEnv := List (Step × Expr)

def lookupExpr (env : ExprEnv) (id : Nat) : Option Expr :=
  (env.find? (fun p => p.1.id == id)).map Prod.snd

def reifyOp (env : ExprEnv) : Op → Option Expr
  | .rat q => some (.rat q)
  | .var => some .var
  | .logTwo => some .logTwo
  | .pi => some .pi
  | .logAtom q _ _ _ => some (.log (.rat q))
  | .atanSmall q _ => some (.atan (.rat q))
  | .atanHalf q _ _ => some (.atan (.rat q))
  | .atanInverse q _ _ => some (.atan (.rat q))
  | .alias a => lookupExpr env a
  | .add a b => do
      let ea ← lookupExpr env a
      let eb ← lookupExpr env b
      return .add ea eb
  | .neg a => (lookupExpr env a).map Expr.neg
  | .mul a b => do
      let ea ← lookupExpr env a
      let eb ← lookupExpr env b
      return .mul ea eb
  | .log a _ _ => (lookupExpr env a).map Expr.log
  | .atan a _ _ => (lookupExpr env a).map Expr.atan
  | .hPositiveProduct a _ => (lookupExpr env a).map Expr.H
  | .hQuarter a _ _ => (lookupExpr env a).map Expr.H
  | .hCross a _ _ => (lookupExpr env a).map Expr.H

def reifyGo (env : ExprEnv) : List Step → Option ExprEnv
  | [] => some env
  | s :: ss =>
      match lookupExpr env s.id, reifyOp env s.op with
      | none, some e => reifyGo ((s, e) :: env) ss
      | _, _ => none

def reifyTrace (steps : List Step) : Option ExprEnv := reifyGo [] steps

end Li2Unified.Proofs.Potential.ReflectionProgram

end

section
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain

open Li2Unified.Proofs.Potential.KernelReflectionSelf

def checkStep (domain : I) (env : List Step) (s : Step) : Bool :=
  let fresh := !(env.any (fun entry => entry.id == s.id))
  fresh && match s.op with
  | .rat q => qValid q && encloses s.out (point q)
  | .var => encloses s.out domain
  | .logTwo => encloses s.out logTwoBounds
  | .pi => encloses s.out piBounds
  | .logAtom q u rho k =>
      qValid q && qValid u && qValid rho &&
      qLT qZero u && qLE u qOne && qLT qZero rho && qLE rho qOne &&
      qEq q (qDiv (qMul (qPow2Z k) u) rho) &&
      encloses s.out (anchoredLogBounds k u rho)
  | .atanSmall q k =>
      qValid q && qLE qZero q && qLT q qOne &&
      encloses s.out (smallAtanBounds q k)
  | .atanHalf q r k =>
      qValid q && qValid r && qLE qZero r && qLE r qHalf &&
      qEq q (qDiv (qAdd qHalf r) (qSub qOne (qMul qHalf r))) &&
      encloses s.out (halfAtanBounds r k)
  | .atanInverse q r j =>
      qValid q && qValid r && qLT qZero q && qEq r (qInv q) &&
      match lookupStep env j with
      | some inv =>
          (atanArgument? env j == some r) && encloses s.out (inverseAtanBounds inv.out)
      | none => false
  | .alias a =>
      match lookup env a with
      | some ia => encloses s.out ia
      | none => false
  | .add a b =>
      match lookup env a, lookup env b with
      | some ia, some ib => encloses s.out (add ia ib)
      | _, _ => false
  | .neg a =>
      match lookup env a with
      | some ia => encloses s.out (neg ia)
      | none => false
  | .mul a b =>
      match lookup env a, lookup env b with
      | some ia, some ib => encloses s.out (mul ia ib)
      | _, _ => false
  | .log a lo hi =>
      match lookup env a, lookup env lo, lookup env hi with
      | some ia, some ilo, some ihi =>
          qLT qZero ia.lo &&
          (logArgument? env lo == some ia.lo) &&
          (logArgument? env hi == some ia.hi) &&
          encloses s.out ⟨ilo.lo, ihi.hi⟩
      | _, _, _ => false
  | .atan a lo hi =>
      match lookup env a, lookup env lo, lookup env hi with
      | some ia, some ilo, some ihi =>
          (atanArgument? env lo == some ia.lo) &&
          (atanArgument? env hi == some ia.hi) &&
          encloses s.out ⟨ilo.lo, ihi.hi⟩
      | _, _, _ => false
  | .hPositiveProduct a witness =>
      match lookup env a, lookupStep env witness with
      | some ia, some w =>
          qLE qZero ia.lo && encloses s.out w.out &&
          match w.op with
          | .mul left logId =>
              (left == a) &&
              match lookupStep env logId with
              | some logStep =>
                  match logStep.op with
                  | .log arg _ _ => arg == a
                  | _ => false
              | none => false
          | _ => false
      | _, _ => false
  | .hQuarter a lo hi =>
      match lookup env a, lookup env lo, lookup env hi with
      | some ia, some ilo, some ihi =>
          qLE qZero ia.lo && qLE ia.hi qQuarter &&
          (logArgument? env lo == some ia.lo) &&
          (logArgument? env hi == some ia.hi) &&
          encloses s.out ⟨qMul ia.hi ihi.lo, qMul ia.lo ilo.hi⟩
      | _, _, _ => false
  | .hCross a logRadius radius =>
      match lookup env a, lookup env logRadius with
      | some ia, some ilog =>
          qValid radius && qLE qZero radius && qLE radius qQuarter &&
          qLE (qNeg radius) ia.lo && qLE ia.hi radius &&
          (logArgument? env logRadius == some radius) &&
          encloses s.out ⟨qMul radius ilog.lo, qNeg (qMul radius ilog.lo)⟩
      | _, _ => false

def checkGo (domain : I) (env : List Step) : List Step → Bool
  | [] => true
  | s :: ss => checkStep domain env s && checkGo domain (s :: env) ss

def checkTrace (domain : I) (steps : List Step) : Bool := checkGo domain [] steps

end Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain

end

section
/-! Pure checker for a compact affine certificate. All point traces are checked
once, at the singleton domain zero. Their expressions are closed before they
are compared with a requested term value. Real soundness is in separate files. -/
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram

structure Prepared where
  stepsRev : List Step
  exprEnv : ExprEnv

def prepareTrace (steps : List Step) : Option Prepared :=
  if KernelReflectionSelf.Domain.checkTrace (point qZero) steps then
    (reifyTrace steps).map (fun env => ⟨steps.reverse, env⟩)
  else none

inductive Term where
  | constant (e : Expr)
  | linear (e : Expr)
  | H (c shift : QPair) (negative : Bool)
  | F (c r : QPair)
  deriving Repr, DecidableEq

def closeAt (x : QPair) : Expr → Expr
  | .rat q => .rat q
  | .var => .rat x
  | .logTwo => .logTwo
  | .pi => .pi
  | .add a b => .add (closeAt x a) (closeAt x b)
  | .neg a => .neg (closeAt x a)
  | .mul a b => .mul (closeAt x a) (closeAt x b)
  | .log a => .log (closeAt x a)
  | .atan a => .atan (closeAt x a)
  | .H a => .H (closeAt x a)

def qAbs (x : QPair) : QPair := if qLE qZero x then x else qNeg x

def pointExpr (t : Term) (x : QPair) : Expr :=
  match t with
  | .constant e => closeAt qZero e
  | .linear e => .mul (closeAt qZero e) (.rat x)
  | .H c shift negative =>
      let u := if negative then qSub shift x else qAdd shift x
      if qEq u qZero then .rat qZero
      else .mul (.rat c) (.mul (.rat u) (.log (.rat (qAbs u))))
  | .F c r =>
      .mul (.rat c) (.add
        (.mul (.rat (qDiv r ⟨2, 1⟩))
          (.log (.rat (qAdd (qMul r r) (qMul x x)))))
        (.neg (.mul (.rat x) (.atan (.rat (qDiv x r))))))

def checkExprPoint (p : Prepared) (e : Expr) (node : Nat) (bound : I) : Bool :=
  (lookupExpr p.exprEnv node == some e) &&
  match lookup p.stepsRev node with
  | some observed => encloses bound observed
  | none => false

def checkPoint (p : Prepared) (t : Term) (x : QPair)
    (node : Nat) (bound : I) : Bool :=
  qValid x &&
  checkExprPoint p (pointExpr t x) node bound

def argument (shift x : QPair) (negative : Bool) : QPair :=
  if negative then qSub shift x else qAdd shift x

def midpoint (a b : QPair) : QPair := qDiv (qAdd a b) ⟨2, 1⟩
def radius (a b : QPair) : QPair := qDiv (qSub b a) ⟨2, 1⟩
def affineAt (a b alpha beta x : QPair) : QPair :=
  qAdd alpha (qMul beta (qSub x (midpoint a b)))

def validTerm : Term → Bool
  | .constant _ => true
  | .linear _ => true
  | .H c shift _ => qValid c && qValid shift
  | .F c r => qValid c && qValid r && qLT qZero r

def convexGuard (t : Term) (a b : QPair) : Bool :=
  validTerm t && qValid a && qValid b && qLE a b &&
  match t with
  | .constant _ | .linear _ => true
  | .H c shift negative =>
      let u := argument shift a negative
      let v := argument shift b negative
      qEq c qZero ||
        (qLE qZero c && qLE qZero u && qLE qZero v) ||
        (qLE c qZero && qLE u qZero && qLE v qZero)
  | .F c _ => qLE c qZero

def concaveGuard (t : Term) (a b : QPair) : Bool :=
  validTerm t && qValid a && qValid b && qLE a b &&
  match t with
  | .constant _ | .linear _ => true
  | .H c shift negative =>
      let u := argument shift a negative
      let v := argument shift b negative
      qEq c qZero ||
        (qLE c qZero && qLE qZero u && qLE qZero v) ||
        (qLE qZero c && qLE u qZero && qLE v qZero)
  | .F c _ => qLE qZero c

def derivativeExpr (t : Term) (x : QPair) : Expr :=
  match t with
  | .constant _ => .rat qZero
  | .linear e => closeAt qZero e
  | .H c shift negative =>
      let u := argument shift x negative
      if qEq c qZero then .rat qZero
      else .mul (.rat (if negative then qNeg c else c))
        (.add (.log (.rat (qAbs u))) (.rat qOne))
  | .F c r => .neg (.mul (.rat c) (.atan (.rat (qDiv x r))))

def derivativeValid (t : Term) (x : QPair) : Bool :=
  match t with
  | .H c shift negative =>
      qEq c qZero || qLT qZero (qAbs (argument shift x negative))
  | _ => true

def checkChord (p : Prepared) (t : Term) (a b alpha beta : QPair)
    (leftNode : Nat) (leftBound : I)
    (rightNode : Nat) (rightBound : I) : Bool :=
  convexGuard t a b && qValid alpha && qValid beta &&
  checkPoint p t a leftNode leftBound &&
  checkPoint p t b rightNode rightBound &&
  qLE leftBound.hi (affineAt a b alpha beta a) &&
  qLE rightBound.hi (affineAt a b alpha beta b)

def checkTangent (p : Prepared) (t : Term) (a b alpha beta : QPair)
    (midNode : Nat) (midBound : I)
    (derivativeNode : Nat) (derivativeBound : I) : Bool :=
  let m := midpoint a b
  let deviation := qMax (qAbs (qSub derivativeBound.lo beta))
                        (qAbs (qSub derivativeBound.hi beta))
  concaveGuard t a b && qValid alpha && qValid beta &&
  checkPoint p t m midNode midBound &&
  derivativeValid t m &&
  checkExprPoint p (derivativeExpr t m) derivativeNode derivativeBound &&
  qLE (qAdd midBound.hi (qMul deviation (radius a b))) alpha

def checkCross (t : Term) (a b alpha beta outer kU rho : QPair)
    (k : Int) : Bool :=
  match t with
  | .H c shift negative =>
      let logBound := anchoredLogBounds k kU rho
      let upper := qMul (qAbs c) (qNeg (qMul outer logBound.lo))
      validTerm t && qValid a && qValid b && qLE a b &&
      qValid alpha && qValid beta &&
      qValid outer && qLT qZero outer && qLE outer qQuarter &&
      qValid kU && qLT qZero kU && qLE kU qOne &&
      qValid rho && qLT qZero rho && qLE rho qOne &&
      qEq outer (qDiv (qMul (qPow2Z k) kU) rho) &&
      validI logBound && qLE logBound.hi qZero &&
      qLE (qNeg outer) (argument shift a negative) &&
      qLE (argument shift a negative) outer &&
      qLE (qNeg outer) (argument shift b negative) &&
      qLE (argument shift b negative) outer &&
      qLE upper (affineAt a b alpha beta a) &&
      qLE upper (affineAt a b alpha beta b)
  | _ => false

inductive PartWitness where
  | chord (leftNode : Nat) (leftBound : I)
      (rightNode : Nat) (rightBound : I)
  | tangent (midNode : Nat) (midBound : I)
      (derivativeNode : Nat) (derivativeBound : I)
  | cross (outer kU rho : QPair) (k : Int)
  deriving Repr

structure PartCert where
  alpha : QPair
  beta : QPair
  witness : PartWitness
  deriving Repr

def checkPart (p : Prepared) (t : Term) (a b : QPair) (part : PartCert) : Bool :=
  match part.witness with
  | .chord ln li rn ri => checkChord p t a b part.alpha part.beta ln li rn ri
  | .tangent mn mi dn di => checkTangent p t a b part.alpha part.beta mn mi dn di
  | .cross outer u rho k => checkCross t a b part.alpha part.beta outer u rho k

def checkParts (p : Prepared) (a b : QPair) : List Term → List PartCert → Bool
  | [], [] => true
  | t :: ts, c :: cs => checkPart p t a b c && checkParts p a b ts cs
  | _, _ => false

structure BoxCert where
  left : QPair
  right : QPair
  alpha : QPair
  beta : QPair
  parts : List PartCert
  deriving Repr

def checkBox (p : Prepared) (terms : List Term) (box : BoxCert) : Bool :=
  qValid box.left && qValid box.right && qLT box.left box.right &&
  qValid box.alpha && qValid box.beta &&
  checkParts p box.left box.right terms box.parts &&
  qEq box.alpha (box.parts.foldl (fun acc part => qAdd acc part.alpha) qZero) &&
  qEq box.beta (box.parts.foldl (fun acc part => qAdd acc part.beta) qZero)

def coverFrom (start finish : QPair) : List BoxCert → Bool
  | [] => qValid start && qValid finish && qEq start finish
  | box :: boxes =>
      qValid start && qValid finish &&
      qValid box.left && qValid box.right &&
      qEq box.left start && qLT box.left box.right &&
      coverFrom box.right finish boxes

end Li2Unified.Proofs.Potential.CompactAffine

end

section
/-! A point trace is interpreted once for each box, then discarded. -/
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf

structure BoxData where
  steps : List Step
  box : BoxCert

def checkOne (terms : List Term) (upper : QPair) (data : BoxData) : Bool :=
  qValid upper &&
  match prepareTrace data.steps with
  | none => false
  | some prepared =>
      checkBox prepared terms data.box &&
      qLE (qAdd data.box.alpha
        (qMul (qAbs data.box.beta) (radius data.box.left data.box.right))) upper

def checkAll (terms : List Term) (upper : QPair) : List BoxData → Bool
  | [] => true
  | data :: rest => checkOne terms upper data && checkAll terms upper rest

end Li2Unified.Proofs.Potential.CompactAffine

end

section
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram

def halfRayLayerData : List (QPair × QPair) := [
  (⟨7, 100⟩, ⟨5486000, 100000027⟩),
  (⟨7, 50⟩, ⟨3870700, 100000027⟩),
  (⟨21, 100⟩, ⟨2913000, 100000027⟩),
  (⟨7, 25⟩, ⟨2327000, 100000027⟩),
  (⟨7, 20⟩, ⟨1932800, 100000027⟩),
  (⟨21, 50⟩, ⟨1648500, 100000027⟩),
  (⟨49, 100⟩, ⟨1433000, 100000027⟩),
  (⟨14, 25⟩, ⟨1263800, 100000027⟩),
  (⟨63, 100⟩, ⟨1127200, 100000027⟩),
  (⟨7, 10⟩, ⟨1014700, 100000027⟩),
  (⟨77, 100⟩, ⟨920500, 100000027⟩),
  (⟨21, 25⟩, ⟨840300, 100000027⟩),
  (⟨91, 100⟩, ⟨771500, 100000027⟩),
  (⟨49, 50⟩, ⟨711800, 100000027⟩),
  (⟨21, 20⟩, ⟨659400, 100000027⟩),
  (⟨28, 25⟩, ⟨613300, 100000027⟩),
  (⟨119, 100⟩, ⟨572300, 100000027⟩),
  (⟨63, 50⟩, ⟨535800, 100000027⟩),
  (⟨133, 100⟩, ⟨503000, 100000027⟩),
  (⟨7, 5⟩, ⟨2230420, 100000027⟩),
  (⟨21, 10⟩, ⟨2947820, 100000027⟩),
  (⟨14, 5⟩, ⟨2013740, 100000027⟩),
  (⟨7, 2⟩, ⟨1498080, 100000027⟩),
  (⟨21, 5⟩, ⟨1181890, 100000027⟩),
  (⟨49, 10⟩, ⟨974840, 100000027⟩),
  (⟨28, 5⟩, ⟨833640, 100000027⟩),
  (⟨63, 10⟩, ⟨735770, 100000027⟩),
  (⟨7, 1⟩, ⟨668860, 100000027⟩),
  (⟨77, 10⟩, ⟨626710, 100000027⟩),
  (⟨42, 5⟩, ⟨607930, 100000027⟩),
  (⟨91, 10⟩, ⟨617440, 100000027⟩),
  (⟨49, 5⟩, ⟨677410, 100000027⟩),
  (⟨21, 2⟩, ⟨958380, 100000027⟩),
  (⟨56, 5⟩, ⟨929970, 100000027⟩)
]

def halfVerticalLayerData : List (QPair × QPair) := [
  (⟨1, 25⟩, ⟨3687200, 100000027⟩),
  (⟨2, 25⟩, ⟨3178600, 100000027⟩)
]

def halfRayDensity : QPair := ⟨46647500, 100000027⟩

def halfConstantExpr : Expr :=
  .add (.mul (.rat ⟨8, 1⟩) .logTwo) (.neg (.rat ⟨4, 1⟩))

def halfRayTerms : List Term :=
  [.constant halfConstantExpr,
   .H ⟨3, 1⟩ qOne false,
   .H ⟨-1, 1⟩ ⟨4, 1⟩ false,
   .H (qSub (qMul ⟨4, 1⟩ halfRayDensity) ⟨2, 1⟩) qZero false,
   .linear (.neg .logTwo)] ++
  halfRayLayerData.map (fun q => .H (qMul ⟨4, 1⟩ q.2) q.1 true) ++
  halfVerticalLayerData.flatMap (fun q =>
    [.F (qMul ⟨8, 1⟩ q.2) q.1,
     .linear (.mul (.rat (qMul ⟨4, 1⟩ q.2)) .pi)])

def halfUpTerms : List Term :=
  [.constant halfConstantExpr,
   .linear (.mul (.rat (qSub (qMul ⟨2, 1⟩ halfRayDensity) qOne)) .pi),
   .F ⟨3, 1⟩ qOne,
   .F ⟨-1, 1⟩ ⟨4, 1⟩] ++
  halfRayLayerData.map (fun q => .F (qMul ⟨4, 1⟩ q.2) q.1) ++
  halfVerticalLayerData.flatMap (fun q =>
    [.H (qMul ⟨4, 1⟩ q.2) q.1 true,
     .H (qMul ⟨4, 1⟩ q.2) q.1 false])

end Li2Unified.Proofs.Potential.CompactAffine

end


end
