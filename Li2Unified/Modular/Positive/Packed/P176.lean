module
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P164
public import Mathlib.Tactic.Linarith
public import Li2Unified.Modular.Positive.Packed.P175
public import Mathlib.Tactic.Tauto

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section

theorem coverFrom_nil_eq {a b : QPair} (h : coverFrom a b [] = true) :
    a.toRat = b.toRat := by
  simp only [coverFrom, Bool.and_eq_true] at h
  exact qEq_sound h.1.1 h.1.2 h.2

theorem coverFrom_contains {start finish : QPair} {boxes : List BoxCert}
    (h : coverFrom start finish boxes = true) (hne : boxes ≠ [])
    {x : ℝ} (hx : (start.toRat : ℝ) ≤ x ∧ x ≤ (finish.toRat : ℝ)) :
    ∃ box ∈ boxes, (box.left.toRat : ℝ) ≤ x ∧ x ≤ (box.right.toRat : ℝ) := by
  induction boxes generalizing start with
  | nil => exact False.elim (hne rfl)
  | cons box boxes ih =>
      simp only [coverFrom, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨hs, hf⟩, hl⟩, hr⟩, heq⟩, hlt⟩, htail⟩ := h
      have hleftQ := qEq_sound hl hs heq
      have hleft : (box.left.toRat : ℝ) = (start.toRat : ℝ) := by
        exact_mod_cast hleftQ
      by_cases hxr : x ≤ (box.right.toRat : ℝ)
      · exact ⟨box, by simp, by simpa only [hleft] using! hx.1, hxr⟩
      · have hxr' : (box.right.toRat : ℝ) < x := lt_of_not_ge hxr
        have hnonempty : boxes ≠ [] := by
          intro he
          subst boxes
          have heqQ := coverFrom_nil_eq htail
          have heqR : (box.right.toRat : ℝ) = (finish.toRat : ℝ) := by
            exact_mod_cast heqQ
          linarith [hx.2]
        obtain ⟨found, hmem, hbound⟩ := ih htail hnonempty ⟨hxr'.le, hx.2⟩
        exact ⟨found, by simp [hmem], hbound⟩

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.coverFrom_contains

end

section
namespace Li2Unified.Proofs.Potential.CompactAffine
open Li2Unified.Proofs.Potential.KernelReflectionSelf
noncomputable section

theorem checkPart_coeff_valid {p : Prepared} {t : Term} {a b : QPair}
    {part : PartCert} (hc : checkPart p t a b part = true) :
    qValid part.alpha = true ∧ qValid part.beta = true := by
  rcases part with ⟨alpha, beta, witness⟩
  cases witness with
  | chord ln li rn ri =>
      simp only [checkPart, checkChord, Bool.and_eq_true] at hc
      tauto
  | tangent mn mi dn di =>
      simp only [checkPart, checkTangent, Bool.and_eq_true] at hc
      tauto
  | cross outer u rho k =>
      cases t <;>
        simp only [checkPart, checkCross, Bool.and_eq_true,
          Bool.false_eq_true] at hc <;> tauto

theorem checkPart_sound {steps : List Step} {p : Prepared}
    {t : Term} {a b : QPair} {part : PartCert}
    (hp : prepareTrace steps = some p)
    (hc : checkPart p t a b part = true)
    (hab : (a.toRat : ℝ) < (b.toRat : ℝ))
    {x : ℝ} (hx : x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) :
    t.eval x ≤ (part.alpha.toRat : ℝ) + (part.beta.toRat : ℝ) *
      (x - ((a.toRat : ℝ) + (b.toRat : ℝ)) / 2) := by
  rcases part with ⟨alpha, beta, witness⟩
  cases witness with
  | chord ln li rn ri => exact checkChord_sound hp hc hab hx
  | tangent mn mi dn di => exact checkTangent_sound hp hc hx
  | cross outer u rho k => exact checkCross_sound hc hx

theorem checkParts_coeff_valid {p : Prepared} {a b : QPair}
    {terms : List Term} {parts : List PartCert}
    (hc : checkParts p a b terms parts = true) :
    ∀ c ∈ parts, qValid c.alpha = true ∧ qValid c.beta = true := by
  induction terms generalizing parts with
  | nil =>
      cases parts with
      | nil => simp
      | cons c cs => simp [checkParts] at hc
  | cons t ts ih =>
      cases parts with
      | nil => simp [checkParts] at hc
      | cons c cs =>
          simp only [checkParts, Bool.and_eq_true] at hc
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact checkPart_coeff_valid hc.1
          · exact ih hc.2 d hd

theorem checkParts_sound {steps : List Step} {p : Prepared}
    {a b : QPair} {terms : List Term} {parts : List PartCert}
    (hp : prepareTrace steps = some p)
    (hc : checkParts p a b terms parts = true)
    (hab : (a.toRat : ℝ) < (b.toRat : ℝ))
    {x : ℝ} (hx : x ∈ Set.Icc (a.toRat : ℝ) (b.toRat : ℝ)) :
    (terms.map (fun t => t.eval x)).sum ≤
      (parts.map (fun c => (c.alpha.toRat : ℝ))).sum +
      (parts.map (fun c => (c.beta.toRat : ℝ))).sum *
        (x - ((a.toRat : ℝ) + (b.toRat : ℝ)) / 2) := by
  induction terms generalizing parts with
  | nil =>
      cases parts with
      | nil => simp
      | cons c cs => simp [checkParts] at hc
  | cons t ts ih =>
      cases parts with
      | nil => simp [checkParts] at hc
      | cons c cs =>
          simp only [checkParts, Bool.and_eq_true] at hc
          have hs := add_le_add (checkPart_sound hp hc.1 hab hx) (ih hc.2)
          simp only [List.map_cons, List.sum_cons]
          convert! hs using 1 <;> ring

private theorem mapped_rat_sum_real {α : Type} (f : α → ℚ) (xs : List α) :
    (((xs.map f).sum : ℚ) : ℝ) = (xs.map (fun y => (f y : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem checkBox_fields {p : Prepared} {terms : List Term} {box : BoxCert}
    (hc : checkBox p terms box = true) :
    qValid box.left = true ∧ qValid box.right = true ∧
      qLT box.left box.right = true ∧ qValid box.alpha = true ∧
      qValid box.beta = true := by
  simp only [checkBox, Bool.and_eq_true] at hc
  tauto

theorem checkBox_sound {steps : List Step} {p : Prepared}
    {terms : List Term} {box : BoxCert}
    (hp : prepareTrace steps = some p)
    (hc : checkBox p terms box = true)
    {x : ℝ} (hx : x ∈ Set.Icc (box.left.toRat : ℝ) (box.right.toRat : ℝ)) :
    (terms.map (fun t => t.eval x)).sum ≤
      (box.alpha.toRat : ℝ) + (box.beta.toRat : ℝ) *
        (x - ((box.left.toRat : ℝ) + (box.right.toRat : ℝ)) / 2) := by
  simp only [checkBox, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hab⟩, halpha⟩, hbeta⟩, hparts⟩, heqa⟩, heqb⟩ := hc
  have hcoeff := checkParts_coeff_valid hparts
  have hva : ∀ c ∈ box.parts, qValid c.alpha = true := fun c hc => (hcoeff c hc).1
  have hvb : ∀ c ∈ box.parts, qValid c.beta = true := fun c hc => (hcoeff c hc).2
  have hfa := fold_qAdd_valid PartCert.alpha box.parts qZero qValid_qZero hva
  have hfb := fold_qAdd_valid PartCert.beta box.parts qZero qValid_qZero hvb
  have heqaQ := qEq_sound halpha hfa heqa
  have heqbQ := qEq_sound hbeta hfb heqb
  have halphaR : (box.alpha.toRat : ℝ) =
      (box.parts.map (fun c => (c.alpha.toRat : ℝ))).sum := by
    rw [heqaQ, fold_qAdd_toRat PartCert.alpha box.parts qZero qValid_qZero hva]
    simp only [qZero_toRat, zero_add, mapped_rat_sum_real]
  have hbetaR : (box.beta.toRat : ℝ) =
      (box.parts.map (fun c => (c.beta.toRat : ℝ))).sum := by
    rw [heqbQ, fold_qAdd_toRat PartCert.beta box.parts qZero qValid_qZero hvb]
    simp only [qZero_toRat, zero_add, mapped_rat_sum_real]
  have habR : (box.left.toRat : ℝ) < (box.right.toRat : ℝ) := by
    exact_mod_cast qLT_sound ha hb hab
  rw [halphaR, hbetaR]
  exact checkParts_sound hp hparts habR hx

theorem checkOne_sound {terms : List Term} {upper : QPair} {data : BoxData}
    (hc : checkOne terms upper data = true)
    {x : ℝ} (hx : x ∈ Set.Icc (data.box.left.toRat : ℝ)
      (data.box.right.toRat : ℝ)) :
    (terms.map (fun t => t.eval x)).sum ≤ (upper.toRat : ℝ) := by
  cases hp : prepareTrace data.steps with
  | none => simp [checkOne, hp] at hc
  | some p =>
      have hh : qValid upper = true ∧
          (checkBox p terms data.box = true ∧
            qLE (qAdd data.box.alpha
              (qMul (qAbs data.box.beta) (radius data.box.left data.box.right)))
              upper = true) := by
        simpa only [checkOne, hp, Bool.and_eq_true] using! hc
      obtain ⟨hu, hbox, hupper⟩ := hh
      obtain ⟨ha, hb, _, halpha, hbeta⟩ := checkBox_fields hbox
      have habs := qAbs_valid' hbeta
      have hrad := radius_valid ha hb
      have hmul := qValid_qMul habs hrad
      have hQ := qLE_sound (qValid_qAdd halpha hmul) hu hupper
      rw [toRat_qAdd _ _ halpha hmul, toRat_qMul,
        qAbs_toRat _ hbeta, radius_toRat ha hb] at hQ
      have hR : (data.box.alpha.toRat : ℝ) + |(data.box.beta.toRat : ℝ)| *
          (((data.box.right.toRat : ℝ) - (data.box.left.toRat : ℝ)) / 2) ≤
            (upper.toRat : ℝ) := by
        exact_mod_cast hQ
      exact (checkBox_sound hp hbox hx).trans
        ((affine_box_upper (alpha := (data.box.alpha.toRat : ℝ))
          (beta := (data.box.beta.toRat : ℝ)) hx).trans hR)

theorem checkAll_one {terms : List Term} {upper : QPair}
    {datas : List BoxData} {data : BoxData}
    (hc : checkAll terms upper datas = true) (hm : data ∈ datas) :
    checkOne terms upper data = true := by
  revert hc hm
  induction datas with
  | nil => intro _ hm; simp at hm
  | cons d ds ih =>
      intro hc hm
      simp only [checkAll, Bool.and_eq_true] at hc
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hc.1
      · exact ih hc.2 hm

theorem checkAll_sound {terms : List Term} {upper : QPair}
    {datas : List BoxData} {data : BoxData}
    (hc : checkAll terms upper datas = true) (hm : data ∈ datas)
    {x : ℝ} (hx : x ∈ Set.Icc (data.box.left.toRat : ℝ)
      (data.box.right.toRat : ℝ)) :
    (terms.map (fun t => t.eval x)).sum ≤ (upper.toRat : ℝ) :=
  checkOne_sound (checkAll_one hc hm) hx

theorem checkAll_cover_sound {terms : List Term} {upper start finish : QPair}
    {datas : List BoxData}
    (hc : checkAll terms upper datas = true)
    (hcover : coverFrom start finish (datas.map BoxData.box) = true)
    (hne : datas ≠ [])
    {x : ℝ} (hx : x ∈ Set.Icc (start.toRat : ℝ) (finish.toRat : ℝ)) :
    (terms.map (fun t => t.eval x)).sum ≤ (upper.toRat : ℝ) := by
  have hmapne : datas.map BoxData.box ≠ [] := by
    cases datas with
    | nil => exact False.elim (hne rfl)
    | cons d ds => simp
  obtain ⟨box, hm, hxb⟩ := coverFrom_contains hcover hmapne hx
  obtain ⟨data, hdata, rfl⟩ := List.mem_map.mp hm
  exact checkAll_sound hc hdata hxb

theorem checkAll_cover_sound_of_lt {terms : List Term} {upper start finish : QPair}
    {datas : List BoxData}
    (hc : checkAll terms upper datas = true)
    (hcover : coverFrom start finish (datas.map BoxData.box) = true)
    (hspan : (start.toRat : ℝ) < (finish.toRat : ℝ))
    {x : ℝ} (hx : x ∈ Set.Icc (start.toRat : ℝ) (finish.toRat : ℝ)) :
    (terms.map (fun t => t.eval x)).sum ≤ (upper.toRat : ℝ) := by
  have hne : datas ≠ [] := by
    intro he
    subst datas
    have heqQ := coverFrom_nil_eq hcover
    have heqR : (start.toRat : ℝ) = (finish.toRat : ℝ) := by
      exact_mod_cast heqQ
    exact (ne_of_lt hspan) heqR
  exact checkAll_cover_sound hc hcover hne hx

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkPart_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkParts_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkBox_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkOne_sound
#print axioms Li2Unified.Proofs.Potential.CompactAffine.checkAll_cover_sound

end

end
