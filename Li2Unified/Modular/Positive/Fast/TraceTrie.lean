module
public import Li2Unified.Modular.Positive.Packed.P110

set_option backward.privateInPublic true

@[expose] public section
namespace Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain

open Li2Unified.Proofs.Potential.KernelReflectionSelf

def lookW (look : Nat → Option Step) (id : Nat) : Option I := (look id).map Step.out

def logArgW (look : Nat → Option Step) (id : Nat) : Option QPair :=
  match look id with
  | some ⟨_, .logAtom q _ _ _, _⟩ => some q
  | _ => none

def atanArgW (look : Nat → Option Step) (id : Nat) : Option QPair :=
  match look id with
  | some ⟨_, .atanSmall q _, _⟩ => some q
  | some ⟨_, .atanHalf q _ _, _⟩ => some q
  | some ⟨_, .atanInverse q _ _, _⟩ => some q
  | some ⟨_, .alias j, _⟩ =>
      match look j with
      | some ⟨_, .atanSmall q _, _⟩ => some q
      | some ⟨_, .atanHalf q _ _, _⟩ => some q
      | some ⟨_, .atanInverse q _ _, _⟩ => some q
      | _ => none
  | _ => none

def checkStepWith (look : Nat → Option Step) (fresh : Bool) (domain : I) (s : Step) : Bool :=
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
      match look j with
      | some inv =>
          (atanArgW look j == some r) && encloses s.out (inverseAtanBounds inv.out)
      | none => false
  | .alias a =>
      match lookW look a with
      | some ia => encloses s.out ia
      | none => false
  | .add a b =>
      match lookW look a, lookW look b with
      | some ia, some ib => encloses s.out (add ia ib)
      | _, _ => false
  | .neg a =>
      match lookW look a with
      | some ia => encloses s.out (neg ia)
      | none => false
  | .mul a b =>
      match lookW look a, lookW look b with
      | some ia, some ib => encloses s.out (mul ia ib)
      | _, _ => false
  | .log a lo hi =>
      match lookW look a, lookW look lo, lookW look hi with
      | some ia, some ilo, some ihi =>
          qLT qZero ia.lo &&
          (logArgW look lo == some ia.lo) &&
          (logArgW look hi == some ia.hi) &&
          encloses s.out ⟨ilo.lo, ihi.hi⟩
      | _, _, _ => false
  | .atan a lo hi =>
      match lookW look a, lookW look lo, lookW look hi with
      | some ia, some ilo, some ihi =>
          (atanArgW look lo == some ia.lo) &&
          (atanArgW look hi == some ia.hi) &&
          encloses s.out ⟨ilo.lo, ihi.hi⟩
      | _, _, _ => false
  | .hPositiveProduct a witness =>
      match lookW look a, look witness with
      | some ia, some w =>
          qLE qZero ia.lo && encloses s.out w.out &&
          match w.op with
          | .mul left logId =>
              (left == a) &&
              match look logId with
              | some logStep =>
                  match logStep.op with
                  | .log arg _ _ => arg == a
                  | _ => false
              | none => false
          | _ => false
      | _, _ => false
  | .hQuarter a lo hi =>
      match lookW look a, lookW look lo, lookW look hi with
      | some ia, some ilo, some ihi =>
          qLE qZero ia.lo && qLE ia.hi qQuarter &&
          (logArgW look lo == some ia.lo) &&
          (logArgW look hi == some ia.hi) &&
          encloses s.out ⟨qMul ia.hi ihi.lo, qMul ia.lo ilo.hi⟩
      | _, _, _ => false
  | .hCross a logRadius radius =>
      match lookW look a, lookW look logRadius with
      | some ia, some ilog =>
          qValid radius && qLE qZero radius && qLE radius qQuarter &&
          qLE (qNeg radius) ia.lo && qLE ia.hi radius &&
          (logArgW look logRadius == some radius) &&
          encloses s.out ⟨qMul radius ilog.lo, qNeg (qMul radius ilog.lo)⟩
      | _, _ => false

/-- Binary trie keyed by the low `d` bits; values live at depth `d`. -/
inductive Trie (α : Type) where
  | nil
  | node (v : Option α) (l r : Trie α)

variable {α : Type}

def Trie.val : Trie α → Option α
  | .nil => none
  | .node v _ _ => v
def Trie.left : Trie α → Trie α
  | .nil => .nil
  | .node _ l _ => l
def Trie.right : Trie α → Trie α
  | .nil => .nil
  | .node _ _ r => r

/-- Structural in `d`, so the kernel reduces it on literals (no well-founded recursion). -/
def Trie.find : Nat → Trie α → Nat → Option α
  | 0, t, _ => t.val
  | d + 1, t, k => if k % 2 = 0 then find d t.left (k / 2) else find d t.right (k / 2)

def Trie.insert : Nat → Trie α → Nat → α → Trie α
  | 0, t, _, s => .node (some s) t.left t.right
  | d + 1, t, k, s =>
      if k % 2 = 0 then .node t.val (insert d t.left (k / 2) s) t.right
      else .node t.val t.left (insert d t.right (k / 2) s)

def trieLook (d : Nat) (t : Trie α) (k : Nat) : Option α :=
  if k < 2 ^ d then t.find d k else none

def fastGo (d : Nat) (domain : I) (t : Trie Step) : List Step → Bool
  | [] => true
  | s :: ss =>
      decide (s.id < 2 ^ d) &&
      checkStepWith (trieLook d t) (trieLook d t s.id).isNone domain s &&
      fastGo d domain (t.insert d s.id s) ss

/-- Every data file has ids exactly 0..N-1 with N ≤ 574, so `d = 10` suffices. -/
def fastCheckTrace (d : Nat) (domain : I) (steps : List Step) : Bool :=
  fastGo d domain .nil steps

/-! ### Soundness: back to the original `Domain.checkTrace`. -/

/-- The only definitional bridge. If `rfl` is slow or fails, fall back to
`cases s with | mk id op out => cases op <;> rfl`. -/
theorem checkStep_eq_with (domain : I) (env : List Step) (s : Step) :
    checkStep domain env s =
      checkStepWith (lookupStep env) (!(env.any (fun entry => entry.id == s.id))) domain s := by
  rfl

theorem Trie.find_nil : ∀ d k, Trie.find d (.nil : Trie α) k = none
  | 0, _ => rfl
  | d + 1, k => by
      unfold Trie.find
      split <;> exact Trie.find_nil d _

theorem Trie.find_insert : ∀ (d : Nat) (t : Trie α) (k k' : Nat) (s : α),
    k < 2 ^ d → k' < 2 ^ d →
      (t.insert d k s).find d k' = if k' = k then some s else t.find d k'
  | 0, t, k, k', s, hk, hk' => by
      have h0 : k = 0 := by simpa using hk
      have h0' : k' = 0 := by simpa using hk'
      subst h0; subst h0'
      simp [Trie.insert, Trie.find, Trie.val]
  | d + 1, t, k, k', s, hk, hk' => by
      have hk2 : k / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk; omega
      have hk2' : k' / 2 < 2 ^ d := by rw [Nat.pow_succ] at hk'; omega
      have ih := Trie.find_insert d
      by_cases hp : k % 2 = 0 <;> by_cases hp' : k' % 2 = 0
      · have e : (k' = k) ↔ (k' / 2 = k / 2) := by omega
        simp only [Trie.insert, Trie.find, hp, hp', if_true, Trie.left]
        rw [ih _ _ _ _ hk2 hk2']
        by_cases h : k' / 2 = k / 2 <;> simp [h, e]
      · have e : k' ≠ k := by omega
        simp [Trie.insert, Trie.find, hp, hp', Trie.right, e]
      · have e : k' ≠ k := by omega
        simp [Trie.insert, Trie.find, hp, hp', Trie.left, e]
      · have e : (k' = k) ↔ (k' / 2 = k / 2) := by omega
        simp only [Trie.insert, Trie.find, hp, hp', if_false, Trie.right]
        rw [ih _ _ _ _ hk2 hk2']
        by_cases h : k' / 2 = k / 2 <;> simp [h, e]

/-- The trie represents `env` exactly, and every id in `env` is below `2^d`. -/
def Rep (d : Nat) (t : Trie Step) (env : List Step) : Prop :=
  (∀ k, k < 2 ^ d → t.find d k = lookupStep env k) ∧ ∀ e ∈ env, e.id < 2 ^ d

theorem rep_nil (d : Nat) : Rep d .nil [] :=
  ⟨fun k _ => by simp [Trie.find_nil, lookupStep], fun _ h => by simp at h⟩

theorem trieLook_eq {d : Nat} {t : Trie Step} {env : List Step} (h : Rep d t env) :
    trieLook d t = lookupStep env := by
  funext k
  unfold trieLook
  split
  · exact h.1 k ‹_›
  · symm
    unfold lookupStep
    rw [List.find?_eq_none]
    intro e he
    have := h.2 e he
    simp only [beq_iff_eq]
    omega

theorem any_eq_isSome_find (env : List Step) (k : Nat) :
    env.any (fun entry => entry.id == k) = (lookupStep env k).isSome := by
  induction env with
  | nil => rfl
  | cons e es ih =>
      simp only [List.any_cons, lookupStep, List.find?_cons] at ih ⊢
      cases h : (e.id == k) <;> simp [h, ih]

theorem rep_insert {d : Nat} {t : Trie Step} {env : List Step} {s : Step}
    (h : Rep d t env) (hs : s.id < 2 ^ d) :
    Rep d (t.insert d s.id s) (s :: env) := by
  refine ⟨fun k hk => ?_, fun e he => ?_⟩
  · rw [Trie.find_insert d t s.id k s hs hk, h.1 k hk]
    simp only [lookupStep, List.find?_cons]
    by_cases hkk : k = s.id
    · subst hkk; simp
    · have : (s.id == k) = false := by simp [beq_iff_eq]; omega
      simp [hkk, this]
  · rcases List.mem_cons.mp he with rfl | he'
    · exact hs
    · exact h.2 e he'

theorem fastGo_sound (d : Nat) (domain : I) :
    ∀ (ss : List Step) (t : Trie Step) (env : List Step), Rep d t env →
      fastGo d domain t ss = true → checkGo domain env ss = true
  | [], _, _, _, _ => rfl
  | s :: ss, t, env, hrep, hgo => by
      simp only [fastGo, Bool.and_eq_true, decide_eq_true_eq] at hgo
      obtain ⟨⟨hid, hstep⟩, hrest⟩ := hgo
      have hlook := trieLook_eq hrep
      have hfresh : (trieLook d t s.id).isNone = !(env.any (fun entry => entry.id == s.id)) := by
        rw [any_eq_isSome_find, hlook]
        cases lookupStep env s.id <;> rfl
      rw [hlook] at hfresh
      rw [hlook, hfresh] at hstep
      simp only [checkGo, Bool.and_eq_true]
      exact ⟨(checkStep_eq_with domain env s).trans hstep,
        fastGo_sound d domain ss _ _ (rep_insert hrep hid) hrest⟩

theorem fastCheckTrace_sound {d : Nat} {domain : I} {steps : List Step}
    (h : fastCheckTrace d domain steps = true) : checkTrace domain steps = true :=
  fastGo_sound d domain steps .nil [] (rep_nil d) h

end Li2Unified.Proofs.Potential.KernelReflectionSelf.Domain

end
