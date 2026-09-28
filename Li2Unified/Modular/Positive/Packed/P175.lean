module
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P169
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Li2Unified.Modular.Positive.Packed.P174
public import Li2Unified.Modular.Positive.Packed.P173
public import Li2Unified.Modular.Positive.Packed.P167
public import Li2Unified.Modular.Positive.Packed.P170

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf

theorem midpoint_valid {a b : QPair} (ha : qValid a = true) (hb : qValid b = true) :
    qValid (midpoint a b) = true :=
  qValid_qDiv_pos (qValid_qAdd ha hb) (by decide)

theorem radius_valid {a b : QPair} (ha : qValid a = true) (hb : qValid b = true) :
    qValid (radius a b) = true :=
  qValid_qDiv_pos (qValid_qSub hb ha) (by decide)

theorem midpoint_toRat {a b : QPair} (ha : qValid a = true) (hb : qValid b = true) :
    (midpoint a b).toRat = (a.toRat+b.toRat)/2 := by
  unfold midpoint
  rw [toRat_qDiv_pos _ _ (by decide), toRat_qAdd a b ha hb]
  norm_num [QPair.toRat]

theorem radius_toRat {a b : QPair} (ha : qValid a = true) (hb : qValid b = true) :
    (radius a b).toRat = (b.toRat-a.toRat)/2 := by
  unfold radius
  rw [toRat_qDiv_pos _ _ (by decide), toRat_qSub b a hb ha]
  norm_num [QPair.toRat]

theorem affineAt_valid {a b alpha beta x : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (halpha : qValid alpha = true) (hbeta : qValid beta = true)
    (hx : qValid x = true) : qValid (affineAt a b alpha beta x) = true :=
  qValid_qAdd halpha (qValid_qMul hbeta (qValid_qSub hx (midpoint_valid ha hb)))

theorem affineAt_toRat {a b alpha beta x : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (halpha : qValid alpha = true) (hbeta : qValid beta = true)
    (hx : qValid x = true) :
    (affineAt a b alpha beta x).toRat =
      alpha.toRat+beta.toRat*(x.toRat-(a.toRat+b.toRat)/2) := by
  unfold affineAt
  rw [toRat_qAdd _ _ halpha (qValid_qMul hbeta (qValid_qSub hx (midpoint_valid ha hb))),
    toRat_qMul, toRat_qSub _ _ hx (midpoint_valid ha hb), midpoint_toRat ha hb]

theorem fold_qAdd_valid {α : Type} (f : α → QPair) (xs : List α) (acc : QPair)
    (ha : qValid acc = true) (hf : ∀ x ∈ xs, qValid (f x) = true) :
    qValid (xs.foldl (fun s x => qAdd s (f x)) acc) = true := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
      exact ih (qAdd acc (f x)) (qValid_qAdd ha (hf x (by simp)))
        (fun y hy => hf y (by simp [hy]))

theorem fold_qAdd_toRat {α : Type} (f : α → QPair) (xs : List α) (acc : QPair)
    (ha : qValid acc = true) (hf : ∀ x ∈ xs, qValid (f x) = true) :
    (xs.foldl (fun s x => qAdd s (f x)) acc).toRat =
      acc.toRat+(xs.map (fun x => (f x).toRat)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (qAdd acc (f x)) (qValid_qAdd ha (hf x (by simp)))
        (fun y hy => hf y (by simp [hy])), toRat_qAdd acc (f x) ha (hf x (by simp))]
      ring

end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.affineAt_toRat
#print axioms Li2Unified.Proofs.Potential.CompactAffine.fold_qAdd_toRat

end

section
/-! One-time real bounds used by the finite affine certificates. -/
namespace Li2Unified.Proofs.Potential.CompactAffine
noncomputable section

theorem convex_chord_upper {f : ℝ → ℝ} {a b x u v : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) (ha : f a ≤ u) (hb : f b ≤ v) :
    f x ≤ (u+v)/2 + ((v-u)/(b-a))*(x-(a+b)/2) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have h0 : 0 ≤ (b-x)/(b-a) := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have h1 : 0 ≤ (x-a)/(b-a) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hs : (b-x)/(b-a)+(x-a)/(b-a) = 1 := by field_simp; ring
  have he : (b-x)/(b-a)*a+(x-a)/(b-a)*b = x := by field_simp; ring
  have h := hf.2 (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
    (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩) h0 h1 hs
  simp only [smul_eq_mul, he] at h
  calc
    f x ≤ (b-x)/(b-a)*f a+(x-a)/(b-a)*f b := h
    _ ≤ (b-x)/(b-a)*u+(x-a)/(b-a)*v :=
      add_le_add (mul_le_mul_of_nonneg_left ha h0) (mul_le_mul_of_nonneg_left hb h1)
    _ = (u+v)/2+((v-u)/(b-a))*(x-(a+b)/2) := by field_simp; ring

theorem concave_tangent_upper {f : ℝ → ℝ} {s : Set ℝ} {m x d : ℝ}
    (hf : ConcaveOn ℝ s f) (hm : m ∈ s) (hx : x ∈ s)
    (hd : HasDerivAt f d m) : f x ≤ f m + d*(x-m) := by
  have hg : ConvexOn ℝ s (-f) := neg_convexOn_iff.mpr hf
  rcases lt_trichotomy m x with h | rfl | h
  · have hs := hg.le_slope_of_hasDerivAt hm hx h hd.neg
    simp only [slope_def_field, Pi.neg_apply] at hs
    have ht := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith
  · simp
  · have hs := hg.slope_le_of_hasDerivAt hx hm h hd.neg
    simp only [slope_def_field, Pi.neg_apply] at hs
    have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

theorem affine_box_upper {a b x alpha beta : ℝ} (hx : x ∈ Set.Icc a b) :
    alpha+beta*(x-(a+b)/2) ≤ alpha+|beta| *((b-a)/2) := by
  have hr : |x-(a+b)/2| ≤ (b-a)/2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have h := mul_le_mul_of_nonneg_left hr (abs_nonneg beta)
  have h' := le_abs_self (beta*(x-(a+b)/2))
  rw [abs_mul] at h'
  linarith

/-- Any affine majorant at the endpoints majorizes a convex function throughout. -/
theorem convex_affine_upper {f : ℝ → ℝ} {a b x alpha beta m : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hf : ConvexOn ℝ (Set.Icc a b) f)
    (ha : f a ≤ alpha+beta*(a-m)) (hb : f b ≤ alpha+beta*(b-m)) :
    f x ≤ alpha+beta*(x-m) := by
  have h := convex_chord_upper hab hx hf ha hb
  have hq : (alpha+beta*(b-m)-(alpha+beta*(a-m)))/(b-a) = beta := by
    apply (div_eq_iff (sub_ne_zero.mpr hab.ne')).2
    ring
  rw [hq] at h
  convert! h using 1 <;> ring

/-- A slope interval permits an arbitrary rational slope in the tangent certificate. -/
theorem tangent_affine_upper {f : ℝ → ℝ} {s : Set ℝ}
    {m x d lo hi u r alpha beta : ℝ}
    (hf : ConcaveOn ℝ s f) (hm : m ∈ s) (hx : x ∈ s)
    (hd : HasDerivAt f d m) (hu : f m ≤ u)
    (hlo : lo ≤ d) (hhi : d ≤ hi) (hr : |x-m| ≤ r)
    (ha : u+max |lo-beta| |hi-beta| * r ≤ alpha) :
    f x ≤ alpha+beta*(x-m) := by
  have hw : 0 ≤ max |lo-beta| |hi-beta| :=
    (abs_nonneg _).trans (le_max_left _ _)
  have he : |d-beta| ≤ max |lo-beta| |hi-beta| := by
    apply abs_le.mpr
    have h0 := (le_abs_self (hi-beta)).trans (le_max_right |lo-beta| |hi-beta|)
    have h1 := (neg_le_abs (lo-beta)).trans (le_max_left |lo-beta| |hi-beta|)
    constructor <;> linarith
  have hb : (d-beta)*(x-m) ≤ max |lo-beta| |hi-beta| * r := by
    calc
      _ ≤ |(d-beta)*(x-m)| := le_abs_self _
      _ = |d-beta| * |x-m| := abs_mul _ _
      _ ≤ max |lo-beta| |hi-beta| * r := mul_le_mul he hr (abs_nonneg _) hw
  have ht := concave_tangent_upper hf hm hx hd
  nlinarith

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.convex_chord_upper
#print axioms Li2Unified.Proofs.Potential.CompactAffine.concave_tangent_upper
#print axioms Li2Unified.Proofs.Potential.CompactAffine.affine_box_upper

#print axioms Li2Unified.Proofs.Potential.CompactAffine.convex_affine_upper
#print axioms Li2Unified.Proofs.Potential.CompactAffine.tangent_affine_upper

end

section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section

theorem qAbs_valid' {q : QPair} (hq : qValid q = true) :
    qValid (qAbs q) = true := by
  unfold qAbs
  split <;> simp_all only [qValid_qNeg]

theorem affineAt_real {a b alpha beta x : QPair}
    (ha : qValid a = true) (hb : qValid b = true)
    (halpha : qValid alpha = true) (hbeta : qValid beta = true)
    (hx : qValid x = true) :
    ((affineAt a b alpha beta x).toRat : ℝ) =
      (alpha.toRat : ℝ)+(beta.toRat : ℝ)*
        ((x.toRat : ℝ)-((a.toRat : ℝ)+(b.toRat : ℝ))/2) := by
  rw [affineAt_toRat ha hb halpha hbeta hx]
  push_cast
  rfl

theorem checkChord_sound {steps : List Step} {p : Prepared}
    {t : Term} {a b alpha beta : QPair} {ln rn : Nat} {li ri : I}
    (hp : prepareTrace steps = some p)
    (hc : checkChord p t a b alpha beta ln li rn ri = true)
    (hab : (a.toRat : ℝ) < (b.toRat : ℝ))
    {x : ℝ} (hx : x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) :
    t.eval x ≤ (alpha.toRat : ℝ)+(beta.toRat : ℝ)*
      (x-((a.toRat : ℝ)+(b.toRat : ℝ))/2) := by
  simp only [checkChord, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hg, halpha⟩, hbeta⟩, hl⟩, hr⟩, hle⟩, hre⟩ := hc
  have hdata := hg
  simp only [convexGuard, Bool.and_eq_true] at hdata
  have ht := hdata.1.1.1.1
  have ha := hdata.1.1.1.2
  have hb := hdata.1.1.2
  obtain ⟨hli, hleft⟩ := checkPoint_eval_sound hp ht hl
  obtain ⟨hri, hright⟩ := checkPoint_eval_sound hp ht hr
  have hleQ := qLE_sound (validI_parts hli).2.1
    (affineAt_valid ha hb halpha hbeta ha) hle
  have hreQ := qLE_sound (validI_parts hri).2.1
    (affineAt_valid ha hb halpha hbeta hb) hre
  have hleR : (li.hi.toRat : ℝ) ≤ (affineAt a b alpha beta a).toRat := by
    exact_mod_cast hleQ
  have hreR : (ri.hi.toRat : ℝ) ≤ (affineAt a b alpha beta b).toRat := by
    exact_mod_cast hreQ
  rw [affineAt_real ha hb halpha hbeta ha] at hleR
  rw [affineAt_real ha hb halpha hbeta hb] at hreR
  exact convex_affine_upper hab hx (convexGuard_sound hg)
    (hleft.2.trans hleR) (hright.2.trans hreR)

theorem checkTangent_sound {steps : List Step} {p : Prepared}
    {t : Term} {a b alpha beta : QPair} {mn dn : Nat} {mi di : I}
    (hp : prepareTrace steps = some p)
    (hc : checkTangent p t a b alpha beta mn mi dn di = true)
    {x : ℝ} (hx : x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) :
    t.eval x ≤ (alpha.toRat : ℝ)+(beta.toRat : ℝ)*
      (x-((a.toRat : ℝ)+(b.toRat : ℝ))/2) := by
  simp only [checkTangent, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hg, halpha⟩, hbeta⟩, hm⟩, hd⟩, he⟩, hu⟩ := hc
  have hdata := hg
  simp only [concaveGuard, Bool.and_eq_true] at hdata
  have ht := hdata.1.1.1.1
  have ha := hdata.1.1.1.2
  have hb := hdata.1.1.2
  have habQ := qLE_sound ha hb hdata.1.2
  have hab : (a.toRat : ℝ) ≤ (b.toRat : ℝ) := by exact_mod_cast habQ
  have hmvalid := midpoint_valid ha hb
  have hrvalid := radius_valid ha hb
  obtain ⟨hmi, hpoint⟩ := checkPoint_eval_sound hp ht hm
  have hdi := checkExprPoint_valid he
  have hder := checkExprPoint_sound hp he
  have hdiff := derivativeExpr_hasDerivAt ht hmvalid hd
  have hmid : ((midpoint a b).toRat : ℝ) =
      ((a.toRat : ℝ)+(b.toRat : ℝ))/2 := by
    rw [midpoint_toRat ha hb]
    push_cast
    rfl
  have hrad : ((radius a b).toRat : ℝ) =
      ((b.toRat : ℝ)-(a.toRat : ℝ))/2 := by
    rw [radius_toRat ha hb]
    push_cast
    rfl
  have hlo := (validI_parts hdi).1
  have hhi := (validI_parts hdi).2.1
  have hdl := qValid_qSub hlo hbeta
  have hdh := qValid_qSub hhi hbeta
  have hdev := qValid_qMax (qAbs_valid' hdl) (qAbs_valid' hdh)
  have huQ := qLE_sound
    (qValid_qAdd (validI_parts hmi).2.1 (qValid_qMul hdev hrvalid)) halpha hu
  rw [toRat_qAdd _ _ (validI_parts hmi).2.1 (qValid_qMul hdev hrvalid),
    toRat_qMul, toRat_qMax _ _ (qAbs_valid' hdl) (qAbs_valid' hdh),
    qAbs_toRat _ hdl, qAbs_toRat _ hdh,
    toRat_qSub _ _ hlo hbeta, toRat_qSub _ _ hhi hbeta,
    radius_toRat ha hb] at huQ
  have huR : (mi.hi.toRat : ℝ)+
      max |(di.lo.toRat : ℝ)-(beta.toRat : ℝ)|
        |(di.hi.toRat : ℝ)-(beta.toRat : ℝ)| *
        (((b.toRat : ℝ)-(a.toRat : ℝ))/2) ≤ (alpha.toRat : ℝ) := by
    exact_mod_cast huQ
  have hmem : ((midpoint a b).toRat : ℝ) ∈
      Set.Icc (a.toRat : ℝ) (b.toRat : ℝ) := by
    rw [hmid]
    constructor <;> linarith
  have hr : |x-((midpoint a b).toRat : ℝ)| ≤
      ((b.toRat : ℝ)-(a.toRat : ℝ))/2 := by
    rw [hmid]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  have h := tangent_affine_upper (concaveGuard_sound hg) hmem hx
    hdiff hpoint.2 hder.1 hder.2 hr huR
  simpa only [hmid] using! h

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkChord_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkTangent_sound

end

section
/-! The special certificate for an H atom crossing its zero. -/
namespace Li2Unified.Proofs.Potential.CompactAffine

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Stage0.HalfPotentialExpressions

noncomputable section

private theorem qAbs_valid (q : QPair) (hq : qValid q = true) :
    qValid (qAbs q) = true := by
  unfold qAbs
  split
  · exact hq
  · exact qValid_qNeg hq

private theorem argument_affine_real (shift x : QPair) (negative : Bool)
    (hs : qValid shift = true) (hx : qValid x = true) :
    ((argument shift x negative).toRat : ℝ) =
      (shift.toRat : ℝ) +
        (if negative then -(x.toRat : ℝ) else (x.toRat : ℝ)) := by
  cases negative with
  | false => simp [argument, toRat_qAdd shift x hs hx]
  | true => simp [argument, toRat_qSub shift x hs hx, sub_eq_add_neg]

private theorem affine_argument_abs_le {a b s R x : ℝ} {negative : Bool}
    (hx : x ∈ Set.Icc a b)
    (halo : -R ≤ s + (if negative then -a else a))
    (hahi : s + (if negative then -a else a) ≤ R)
    (hblo : -R ≤ s + (if negative then -b else b))
    (hbhi : s + (if negative then -b else b) ≤ R) :
    |s + (if negative then -x else x)| ≤ R := by
  cases negative <;> simp only [Bool.false_eq_true,
    if_false, if_true] at *
  · apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]
  · apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2]

private theorem H_cross_bound {c u R L : ℝ}
    (hu : |u| ≤ R) (hR : R ≤ 1 / 4) (hR0 : 0 ≤ R)
    (hlog : L ≤ Real.log R) :
    c * H u ≤ |c| * (-R * L) := by
  calc
    c * H u ≤ |c * H u| := le_abs_self _
    _ ≤ |c| * (-R * Real.log R) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (H_cross_zero hu hR) (abs_nonneg c)
    _ ≤ |c| * (-R * L) := by
      have hmul : (-R) * Real.log R ≤ (-R) * L :=
        mul_le_mul_of_nonpos_left hlog (by linarith)
      exact mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg c)

theorem checkCross_sound {t : Term} {a b alpha beta outer kU rho : QPair}
    {k : Int} {x : ℝ}
    (hcheck : checkCross t a b alpha beta outer kU rho k = true)
    (hx : x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) :
    t.eval x ≤ (alpha.toRat : ℝ) + (beta.toRat : ℝ) *
      (x - ((a.toRat : ℝ) + (b.toRat : ℝ)) / 2) := by
  cases t with
  | constant e => simp only [checkCross, Bool.false_eq_true] at hcheck
  | linear e => simp only [checkCross, Bool.false_eq_true] at hcheck
  | F c r => simp only [checkCross, Bool.false_eq_true] at hcheck
  | H c shift negative =>
      simp only [checkCross, Bool.and_eq_true, and_assoc] at hcheck
      obtain ⟨ht, ha, hb, _hab, halpha, hbeta, houter, houter0, hquarter,
        hku, hku0, hku1, hrho, hrho0, hrho1, heq, hlogvalid,
        _hloghi, halo, hahi, hblo, hbhi, hupperleft, hupperright⟩ := hcheck
      have hterm : qValid c = true ∧ qValid shift = true := by
        simpa only [validTerm, Bool.and_eq_true] using! ht
      obtain ⟨hc, hs⟩ := hterm
      let logBound := KernelReflectionSelf.anchoredLogBounds k kU rho
      let upper := qMul (qAbs c) (qNeg (qMul outer logBound.lo))
      have hloValid : qValid logBound.lo = true := (validI_parts hlogvalid).1
      have hupperValid : qValid upper = true :=
        qValid_qMul (qAbs_valid c hc)
          (qValid_qNeg (qValid_qMul houter hloValid))
      have qle {u v : QPair} (hu : qValid u = true) (hv : qValid v = true)
          (h : qLE u v = true) : (u.toRat : ℝ) ≤ (v.toRat : ℝ) := by
        exact_mod_cast qLE_sound hu hv h
      have hR0 : (0 : ℝ) ≤ (outer.toRat : ℝ) := by
        have h := qLT_sound qValid_qZero houter houter0
        rw [qZero_toRat] at h
        exact le_of_lt (by exact_mod_cast h)
      have hRq : (outer.toRat : ℝ) ≤ 1 / 4 := by
        have h := qle houter (by decide : qValid qQuarter = true) hquarter
        norm_num [qQuarter_toRat] at h ⊢
        exact h
      have hargA := argument_valid shift a negative hs ha
      have hargB := argument_valid shift b negative hs hb
      have haloR := qle (qValid_qNeg houter) hargA halo
      have hahiR := qle hargA houter hahi
      have hbloR := qle (qValid_qNeg houter) hargB hblo
      have hbhiR := qle hargB houter hbhi
      rw [toRat_qNeg, Rat.cast_neg,
        argument_affine_real shift a negative hs ha] at haloR
      rw [argument_affine_real shift a negative hs ha] at hahiR
      rw [toRat_qNeg, Rat.cast_neg,
        argument_affine_real shift b negative hs hb] at hbloR
      rw [argument_affine_real shift b negative hs hb] at hbhiR
      have hu : |(shift.toRat : ℝ) + (if negative then -x else x)| ≤
          (outer.toRat : ℝ) :=
        affine_argument_abs_le hx haloR hahiR hbloR hbhiR
      have hlog : logBound.toBounds.Contains (Real.log (outer.toRat : ℝ)) :=
        contains_logAtom houter hku hrho hku0 hku1 hrho0 hrho1 heq
      have hloglo : (logBound.lo.toRat : ℝ) ≤ Real.log (outer.toRat : ℝ) := hlog.1
      have hupperReal : (upper.toRat : ℝ) =
          |(c.toRat : ℝ)| * (-(outer.toRat : ℝ) * (logBound.lo.toRat : ℝ)) := by
        dsimp only [upper]
        rw [toRat_qMul, qAbs_toRat c hc, toRat_qNeg, toRat_qMul]
        push_cast
        ring
      have hbase : (Term.H c shift negative).eval x ≤ (upper.toRat : ℝ) := by
        rw [hupperReal]
        exact H_cross_bound (c := (c.toRat : ℝ)) hu hRq hR0 hloglo
      have hleft : (upper.toRat : ℝ) ≤
          ((affineAt a b alpha beta a).toRat : ℝ) :=
        qle hupperValid (affineAt_valid ha hb halpha hbeta ha) hupperleft
      have hright : (upper.toRat : ℝ) ≤
          ((affineAt a b alpha beta b).toRat : ℝ) :=
        qle hupperValid (affineAt_valid ha hb halpha hbeta hb) hupperright
      rw [affineAt_toRat ha hb halpha hbeta ha] at hleft
      rw [affineAt_toRat ha hb halpha hbeta hb] at hright
      push_cast at hleft hright
      have hupperx : (upper.toRat : ℝ) ≤
          (alpha.toRat : ℝ) + (beta.toRat : ℝ) *
            (x - ((a.toRat : ℝ) + (b.toRat : ℝ)) / 2) := by
        by_cases hbeta0 : (0 : ℝ) ≤ (beta.toRat : ℝ)
        · have hm := mul_nonneg hbeta0 (sub_nonneg.mpr hx.1)
          nlinarith [hleft]
        · have hm := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hbeta0)
            (sub_nonpos.mpr hx.2)
          nlinarith [hright]
      exact hbase.trans hupperx

#print axioms checkCross_sound

end
end Li2Unified.Proofs.Potential.CompactAffine

end

end
