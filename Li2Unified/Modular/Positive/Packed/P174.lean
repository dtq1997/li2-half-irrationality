module
public import Li2Unified.Modular.Positive.Packed.P167
public import Li2Unified.Modular.Positive.Packed.P173
public import Li2Unified.Modular.Positive.Packed.P169

set_option backward.privateInPublic true

@[expose] public section

section
/-! Real curvature and derivative facts for the compact affine terms. -/
namespace Li2Unified.Proofs.Potential.CompactAffine
noncomputable section

open Li2Unified.Proofs.Potential.KernelReflectionSelf
open Li2Unified.Proofs.Potential.ReflectionProgram

private theorem qLE_real {u v : QPair} (hu : qValid u = true)
    (hv : qValid v = true) (h : qLE u v = true) :
    (u.toRat : ℝ) ≤ (v.toRat : ℝ) := by
  exact_mod_cast qLE_sound hu hv h

private theorem qLT_real {u v : QPair} (hu : qValid u = true)
    (hv : qValid v = true) (h : qLT u v = true) :
    (u.toRat : ℝ) < (v.toRat : ℝ) := by
  exact_mod_cast qLT_sound hu hv h

private theorem termH_hasDerivAt (c shift : QPair) (negative : Bool)
    (x : ℝ)
    (hu : (shift.toRat : ℝ) + (if negative then -x else x) ≠ 0) :
    HasDerivAt ((Term.H c shift negative).eval)
      ((c.toRat : ℝ) *
        ((Real.log |(shift.toRat : ℝ) + (if negative then -x else x)| + 1) *
          (if negative then (-1 : ℝ) else 1))) x := by
  cases negative with
  | false =>
      simpa [Term.eval] using
        hasDerivAt_affineH (shift.toRat : ℝ) 1 (c.toRat : ℝ) x (by simpa using hu)
  | true =>
      simpa [Term.eval] using
        hasDerivAt_affineH (shift.toRat : ℝ) (-1) (c.toRat : ℝ) x (by simpa using hu)

private theorem termF_hasDerivAt (c r : QPair) (x : ℝ)
    (hr : 0 < (r.toRat : ℝ)) :
    HasDerivAt ((Term.F c r).eval)
      ((c.toRat : ℝ) * (-Real.arctan (x / (r.toRat : ℝ)))) x := by
  simpa only [Term.eval] using (F_hasDerivAt hr x).const_mul (c.toRat : ℝ)

private theorem scaledF_concaveOn_Icc (a b r c : ℝ)
    (hr : 0 < r) (hc : 0 ≤ c) :
    ConcaveOn ℝ (Set.Icc a b) (fun x : ℝ => c * F r x) := by
  have hf : ConcaveOn ℝ (Set.Icc a b) (F r) :=
    (F_concaveOn hr).subset (Set.subset_univ _) (convex_Icc a b)
  simpa only [smul_eq_mul] using (ConcaveOn.smul hc hf)

private theorem scaledF_convexOn_Icc (a b r c : ℝ)
    (hr : 0 < r) (hc : c ≤ 0) :
    ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => c * F r x) := by
  have h := (scaledF_concaveOn_Icc a b r (-c) hr (neg_nonneg.mpr hc)).neg
  exact h.congr (by
    intro x hx
    simp only [Pi.neg_apply]
    ring)

private theorem coeff_nonneg {c : QPair} (hc : qValid c = true)
    (h : qLE qZero c = true) : 0 ≤ (c.toRat : ℝ) := by
  simpa [qZero_toRat] using qLE_real qValid_qZero hc h

private theorem coeff_nonpos {c : QPair} (hc : qValid c = true)
    (h : qLE c qZero = true) : (c.toRat : ℝ) ≤ 0 := by
  simpa [qZero_toRat] using qLE_real hc qValid_qZero h

private theorem coeff_zero {c : QPair} (hc : qValid c = true)
    (h : qEq c qZero = true) : (c.toRat : ℝ) = 0 := by
  have hq := qEq_sound hc qValid_qZero h
  exact_mod_cast (by simpa only [qZero_toRat] using hq)

private theorem argument_affine_real (shift x : QPair) (negative : Bool)
    (hs : qValid shift = true) (hx : qValid x = true) :
    ((argument shift x negative).toRat : ℝ) =
      (shift.toRat : ℝ) +
        (if negative then (-1 : ℝ) else 1) * (x.toRat : ℝ) := by
  rw [argument_toRat shift x negative hs hx]
  cases negative <;> norm_num

private theorem argument_nonneg_real (shift x : QPair) (negative : Bool)
    (hs : qValid shift = true) (hx : qValid x = true)
    (h : qLE qZero (argument shift x negative) = true) :
    0 ≤ (shift.toRat : ℝ) +
      (if negative then (-1 : ℝ) else 1) * (x.toRat : ℝ) := by
  have harg := argument_valid shift x negative hs hx
  have hreal : (0 : ℝ) ≤ ((argument shift x negative).toRat : ℝ) := by
    simpa [qZero_toRat] using qLE_real qValid_qZero harg h
  rwa [argument_affine_real shift x negative hs hx] at hreal

private theorem argument_nonpos_real (shift x : QPair) (negative : Bool)
    (hs : qValid shift = true) (hx : qValid x = true)
    (h : qLE (argument shift x negative) qZero = true) :
    (shift.toRat : ℝ) +
      (if negative then (-1 : ℝ) else 1) * (x.toRat : ℝ) ≤ 0 := by
  have harg := argument_valid shift x negative hs hx
  have hreal : ((argument shift x negative).toRat : ℝ) ≤ 0 := by
    simpa [qZero_toRat] using qLE_real harg qValid_qZero h
  rwa [argument_affine_real shift x negative hs hx] at hreal

private theorem convexGuard_data {t : Term} {a b : QPair}
    (h : convexGuard t a b = true) :
    validTerm t = true ∧ qValid a = true ∧ qValid b = true ∧ qLE a b = true := by
  simp only [convexGuard, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

private theorem concaveGuard_data {t : Term} {a b : QPair}
    (h : concaveGuard t a b = true) :
    validTerm t = true ∧ qValid a = true ∧ qValid b = true ∧ qLE a b = true := by
  simp only [concaveGuard, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem convexGuard_sound {t : Term} {a b : QPair}
    (h : convexGuard t a b = true) :
    ConvexOn ℝ (Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) (Term.eval t) := by
  obtain ⟨ht, ha, hb, _⟩ := convexGuard_data h
  cases t with
  | constant e =>
      simpa only [Term.eval] using
        (convexOn_const (e.denote 0) (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ)))
  | linear e =>
      refine ⟨convex_Icc _ _, ?_⟩
      intro x hx y hy u v hu hv huv
      simp only [Term.eval, smul_eq_mul]
      apply le_of_eq
      ring
  | H c shift negative =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨hc, hs⟩ := ht
      have hh := h
      simp only [convexGuard, Bool.and_eq_true, Bool.or_eq_true] at hh
      rcases hh.2 with (hz | hpos) | hneg
      · have hc0 := coeff_zero hc hz
        have hconst : ConvexOn ℝ (Set.Icc (a.toRat : ℝ) (b.toRat : ℝ))
            (fun _ : ℝ => (0 : ℝ)) :=
          convexOn_const (0 : ℝ) (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ))
        have hfun : (Term.H c shift negative).eval = fun _ : ℝ => 0 := by
          funext x
          simp [Term.eval, hc0]
        rw [hfun]
        exact hconst
      · rcases hpos with ⟨⟨hcoeff, hleft⟩, hright⟩
        have hside : ∀ x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ),
            0 ≤ (shift.toRat : ℝ) +
              (if negative then (-1 : ℝ) else 1) * x :=
          affine_nonneg_on_Icc _ _ _ _
            (argument_nonneg_real shift a negative hs ha hleft)
            (argument_nonneg_real shift b negative hs hb hright)
        have hcore := affineH_convex_nonneg
          (s := Set.Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (shift.toRat : ℝ) (if negative then (-1 : ℝ) else 1)
          (c.toRat : ℝ) hside (coeff_nonneg hc hcoeff)
        cases negative <;> simpa [Term.eval] using hcore
      · rcases hneg with ⟨⟨hcoeff, hleft⟩, hright⟩
        have hside : ∀ x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ),
            (shift.toRat : ℝ) +
              (if negative then (-1 : ℝ) else 1) * x ≤ 0 :=
          affine_nonpos_on_Icc _ _ _ _
            (argument_nonpos_real shift a negative hs ha hleft)
            (argument_nonpos_real shift b negative hs hb hright)
        have hcore := affineH_convex_nonpos
          (s := Set.Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (shift.toRat : ℝ) (if negative then (-1 : ℝ) else 1)
          (c.toRat : ℝ) hside (coeff_nonpos hc hcoeff)
        cases negative <;> simpa [Term.eval] using hcore
  | F c r =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨⟨hc, hr⟩, hrpos⟩ := ht
      have hh := h
      simp only [convexGuard, Bool.and_eq_true] at hh
      have hcneg : (c.toRat : ℝ) ≤ 0 := coeff_nonpos hc hh.2
      have hrreal : 0 < (r.toRat : ℝ) := by
        simpa [qZero_toRat] using qLT_real qValid_qZero hr hrpos
      simpa only [Term.eval] using
        scaledF_convexOn_Icc (a.toRat : ℝ) (b.toRat : ℝ)
          (r.toRat : ℝ) (c.toRat : ℝ) hrreal hcneg

theorem concaveGuard_sound {t : Term} {a b : QPair}
    (h : concaveGuard t a b = true) :
    ConcaveOn ℝ (Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) (Term.eval t) := by
  obtain ⟨ht, ha, hb, _⟩ := concaveGuard_data h
  cases t with
  | constant e =>
      simpa only [Term.eval] using
        (concaveOn_const (e.denote 0) (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ)))
  | linear e =>
      refine ⟨convex_Icc _ _, ?_⟩
      intro x hx y hy u v hu hv huv
      simp only [Term.eval, smul_eq_mul]
      apply le_of_eq
      ring
  | H c shift negative =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨hc, hs⟩ := ht
      have hh := h
      simp only [concaveGuard, Bool.and_eq_true, Bool.or_eq_true] at hh
      rcases hh.2 with (hz | hpos) | hneg
      · have hc0 := coeff_zero hc hz
        have hconst : ConcaveOn ℝ (Set.Icc (a.toRat : ℝ) (b.toRat : ℝ))
            (fun _ : ℝ => (0 : ℝ)) :=
          concaveOn_const (0 : ℝ) (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ))
        have hfun : (Term.H c shift negative).eval = fun _ : ℝ => 0 := by
          funext x
          simp [Term.eval, hc0]
        rw [hfun]
        exact hconst
      · rcases hpos with ⟨⟨hcoeff, hleft⟩, hright⟩
        have hside : ∀ x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ),
            0 ≤ (shift.toRat : ℝ) +
              (if negative then (-1 : ℝ) else 1) * x :=
          affine_nonneg_on_Icc _ _ _ _
            (argument_nonneg_real shift a negative hs ha hleft)
            (argument_nonneg_real shift b negative hs hb hright)
        have hcore := affineH_concave_nonneg
          (s := Set.Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (shift.toRat : ℝ) (if negative then (-1 : ℝ) else 1)
          (c.toRat : ℝ) hside (coeff_nonpos hc hcoeff)
        cases negative <;> simpa [Term.eval] using hcore
      · rcases hneg with ⟨⟨hcoeff, hleft⟩, hright⟩
        have hside : ∀ x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ),
            (shift.toRat : ℝ) +
              (if negative then (-1 : ℝ) else 1) * x ≤ 0 :=
          affine_nonpos_on_Icc _ _ _ _
            (argument_nonpos_real shift a negative hs ha hleft)
            (argument_nonpos_real shift b negative hs hb hright)
        have hcore := affineH_concave_nonpos
          (s := Set.Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (convex_Icc (a.toRat : ℝ) (b.toRat : ℝ))
          (shift.toRat : ℝ) (if negative then (-1 : ℝ) else 1)
          (c.toRat : ℝ) hside (coeff_nonneg hc hcoeff)
        cases negative <;> simpa [Term.eval] using hcore
  | F c r =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨⟨hc, hr⟩, hrpos⟩ := ht
      have hh := h
      simp only [concaveGuard, Bool.and_eq_true] at hh
      have hcpos : 0 ≤ (c.toRat : ℝ) := coeff_nonneg hc hh.2
      have hrreal : 0 < (r.toRat : ℝ) := by
        simpa [qZero_toRat] using qLT_real qValid_qZero hr hrpos
      simpa only [Term.eval] using
        scaledF_concaveOn_Icc (a.toRat : ℝ) (b.toRat : ℝ)
          (r.toRat : ℝ) (c.toRat : ℝ) hrreal hcpos

private theorem qAbs_valid (u : QPair) (hu : qValid u = true) :
    qValid (qAbs u) = true := by
  unfold qAbs
  split_ifs
  · exact hu
  · exact qValid_qNeg hu

theorem derivativeExpr_hasDerivAt {t : Term} {m : QPair}
    (ht : validTerm t = true) (hm : qValid m = true)
    (hd : derivativeValid t m = true) :
    HasDerivAt (Term.eval t) ((derivativeExpr t m).denote 0) (m.toRat : ℝ) := by
  cases t with
  | constant e =>
      simpa [Term.eval, derivativeExpr, Expr.denote, qZero_toRat] using
        (hasDerivAt_const (m.toRat : ℝ) (e.denote 0))
  | linear e =>
      simpa [Term.eval, derivativeExpr, closeAt_denote, qZero_toRat] using
        ((hasDerivAt_id (m.toRat : ℝ)).const_mul (e.denote 0))
  | H c shift negative =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨hc, hs⟩ := ht
      by_cases hz : qEq c qZero = true
      · have hc0 := coeff_zero hc hz
        have hfun : (Term.H c shift negative).eval = fun _ : ℝ => 0 := by
          funext x
          simp [Term.eval, hc0]
        rw [hfun]
        simpa [derivativeExpr, hz, Expr.denote, qZero_toRat, hc0] using
          (hasDerivAt_const (m.toRat : ℝ) (0 : ℝ))
      · let u := argument shift m negative
        have hu : qValid u = true := argument_valid shift m negative hs hm
        have hpos : qLT qZero (qAbs u) = true := by
          simpa [derivativeValid, hz, u] using hd
        have habs : ((qAbs u).toRat : ℝ) = |(u.toRat : ℝ)| := by
          rw [qAbs_toRat u hu]
          norm_cast
        have hu0 : (u.toRat : ℝ) ≠ 0 := by
          have hq := qLT_sound qValid_qZero (qAbs_valid u hu) hpos
          have hr : (0 : ℝ) < ((qAbs u).toRat : ℝ) := by
            have hqr : (qZero.toRat : ℝ) < ((qAbs u).toRat : ℝ) := by
              exact_mod_cast hq
            simpa [qZero_toRat] using hqr
          rw [habs] at hr
          exact abs_pos.mp hr
        have harg : (u.toRat : ℝ) =
            (shift.toRat : ℝ) +
              (if negative then -((m.toRat : ℝ)) else (m.toRat : ℝ)) := by
          dsimp [u]
          rw [argument_toRat shift m negative hs hm]
          cases negative <;> norm_num
        have harg0 : (shift.toRat : ℝ) +
            (if negative then -((m.toRat : ℝ)) else (m.toRat : ℝ)) ≠ 0 := by
          rwa [← harg]
        have hbase := termH_hasDerivAt c shift negative (m.toRat : ℝ) harg0
        have hvalue : (derivativeExpr (Term.H c shift negative) m).denote 0 =
            (c.toRat : ℝ) *
              ((Real.log |(shift.toRat : ℝ) +
                (if negative then -((m.toRat : ℝ)) else (m.toRat : ℝ))| + 1) *
                  (if negative then (-1 : ℝ) else 1)) := by
          cases negative with
          | false =>
              simp [derivativeExpr, hz, Expr.denote, u, habs, qOne_toRat, harg]
          | true =>
              simp [derivativeExpr, hz, Expr.denote, u, habs, qOne_toRat,
                harg, toRat_qNeg]
              ring
        simpa only [hvalue] using hbase
  | F c r =>
      simp only [validTerm, Bool.and_eq_true] at ht
      obtain ⟨⟨_, hr⟩, hrpos⟩ := ht
      have hrreal : 0 < (r.toRat : ℝ) := by
        simpa [qZero_toRat] using qLT_real qValid_qZero hr hrpos
      have hbase := termF_hasDerivAt c r (m.toRat : ℝ) hrreal
      have hquot : ((qDiv m r).toRat : ℝ) =
          (m.toRat : ℝ) / (r.toRat : ℝ) := by
        rw [toRat_qDiv_pos m r hrpos]
        push_cast
        rfl
      simpa [derivativeExpr, Expr.denote, hquot, neg_mul] using hbase

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.convexGuard_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.concaveGuard_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.derivativeExpr_hasDerivAt

end


end
