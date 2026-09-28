module
public import Li2Unified.Modular.Positive.Packed.P110
public import Li2Unified.Modular.Positive.Packed.P164
public import Li2Unified.Modular.Positive.Packed.P166

set_option backward.privateInPublic true

@[expose] public section

section
/-! Real meaning of the four compact affine term constructors. -/
namespace Li2Unified.Proofs.Potential.CompactAffine
noncomputable section

open Li2Unified.Proofs.Potential.ReflectionProgram

def Term.eval (t : Term) (x : ℝ) : ℝ :=
  match t with
  | .constant e => e.denote 0
  | .linear e => e.denote 0 * x
  | .H c shift negative =>
      (c.toRat : ℝ) *
        Li2Unified.Stage0.HalfPotentialExpressions.H
          ((shift.toRat : ℝ) + (if negative then -x else x))
  | .F c r => (c.toRat : ℝ) *
      Li2Unified.Proofs.Potential.CompactAffine.F (r.toRat : ℝ) x

end
end Li2Unified.Proofs.Potential.CompactAffine

end

section
namespace Li2Unified.Proofs.Potential.CompactAffine
noncomputable section
open Li2Unified.Stage0.HalfPotentialExpressions

private lemma H_neg (u : ℝ) : H (-u) = -H u := by
  simp only [H, abs_neg, neg_mul]

theorem H_convexOn_nonneg : ConvexOn ℝ (Set.Ici (0 : ℝ)) H := by
  apply Real.convexOn_mul_log.congr
  intro u hu
  simp only [Set.mem_Ici] at hu
  simp only [H, abs_of_nonneg hu]

theorem H_concaveOn_nonpos : ConcaveOn ℝ (Set.Iic (0 : ℝ)) H := by
  refine ⟨convex_Iic 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : -x ∈ Set.Ici (0 : ℝ) := by
    simpa only [Set.mem_Ici] using! (neg_nonneg.mpr hx)
  have hy' : -y ∈ Set.Ici (0 : ℝ) := by
    simpa only [Set.mem_Ici] using! (neg_nonneg.mpr hy)
  have h := H_convexOn_nonneg.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a * -x + b * -y = -(a*x+b*y) := by ring
  rw [he, H_neg, H_neg, H_neg] at h
  linarith

theorem affineH_convex_nonneg {s : Set ℝ} (hs : Convex ℝ s)
    (r slope c : ℝ) (hpos : ∀ t ∈ s, 0 ≤ r + slope*t) (hc : 0 ≤ c) :
    ConvexOn ℝ s (fun t : ℝ => c * H (r + slope*t)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbase := H_convexOn_nonneg.2
    (show r + slope*x ∈ Set.Ici (0 : ℝ) from hpos x hx)
    (show r + slope*y ∈ Set.Ici (0 : ℝ) from hpos y hy) ha hb hab
  simp only [smul_eq_mul] at hbase ⊢
  have he : r + slope*(a*x+b*y) =
      a*(r+slope*x)+b*(r+slope*y) := by
    calc
      r + slope*(a*x+b*y) = (a+b)*r + slope*(a*x+b*y) := by rw [hab]; ring
      _ = a*(r+slope*x)+b*(r+slope*y) := by ring
  rw [he]
  calc
    c * H (a*(r+slope*x)+b*(r+slope*y)) ≤
        c * (a*H (r+slope*x)+b*H (r+slope*y)) :=
      mul_le_mul_of_nonneg_left hbase hc
    _ = a*(c*H (r+slope*x))+b*(c*H (r+slope*y)) := by ring

theorem affineH_concave_nonpos {s : Set ℝ} (hs : Convex ℝ s)
    (r slope c : ℝ) (hneg : ∀ t ∈ s, r + slope*t ≤ 0) (hc : 0 ≤ c) :
    ConcaveOn ℝ s (fun t : ℝ => c * H (r + slope*t)) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbase := H_concaveOn_nonpos.2
    (show r + slope*x ∈ Set.Iic (0 : ℝ) from hneg x hx)
    (show r + slope*y ∈ Set.Iic (0 : ℝ) from hneg y hy) ha hb hab
  simp only [smul_eq_mul] at hbase ⊢
  have he : r + slope*(a*x+b*y) =
      a*(r+slope*x)+b*(r+slope*y) := by
    calc
      r + slope*(a*x+b*y) = (a+b)*r + slope*(a*x+b*y) := by rw [hab]; ring
      _ = a*(r+slope*x)+b*(r+slope*y) := by ring
  rw [he]
  calc
    a*(c*H (r+slope*x))+b*(c*H (r+slope*y)) =
        c*(a*H (r+slope*x)+b*H (r+slope*y)) := by ring
    _ ≤ c*H (a*(r+slope*x)+b*(r+slope*y)) :=
      mul_le_mul_of_nonneg_left hbase hc

theorem affineH_concave_nonneg {s : Set ℝ} (hs : Convex ℝ s)
    (r slope c : ℝ) (hpos : ∀ t ∈ s, 0 ≤ r + slope*t) (hc : c ≤ 0) :
    ConcaveOn ℝ s (fun t : ℝ => c * H (r + slope*t)) := by
  have h := (affineH_convex_nonneg hs r slope (-c) hpos (neg_nonneg.mpr hc)).neg
  exact h.congr (by
    intro t ht
    simp only [Pi.neg_apply]
    ring)

theorem affineH_convex_nonpos {s : Set ℝ} (hs : Convex ℝ s)
    (r slope c : ℝ) (hneg : ∀ t ∈ s, r + slope*t ≤ 0) (hc : c ≤ 0) :
    ConvexOn ℝ s (fun t : ℝ => c * H (r + slope*t)) := by
  have h := (affineH_concave_nonpos hs r slope (-c) hneg (neg_nonneg.mpr hc)).neg
  exact h.congr (by
    intro t ht
    simp only [Pi.neg_apply]
    ring)

theorem affine_nonneg_on_Icc (a b r slope : ℝ)
    (ha : 0 ≤ r + slope*a) (hb : 0 ≤ r + slope*b) :
    ∀ t ∈ Set.Icc a b, 0 ≤ r + slope*t := by
  intro t ht
  by_cases hs : 0 ≤ slope
  · have h := mul_nonneg hs (sub_nonneg.mpr ht.1)
    nlinarith
  · have hs' : slope ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have h := mul_nonneg_of_nonpos_of_nonpos hs' (sub_nonpos.mpr ht.2)
    nlinarith

theorem affine_nonpos_on_Icc (a b r slope : ℝ)
    (ha : r + slope*a ≤ 0) (hb : r + slope*b ≤ 0) :
    ∀ t ∈ Set.Icc a b, r + slope*t ≤ 0 := by
  intro t ht
  by_cases hs : 0 ≤ slope
  · have h := mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr ht.2)
    nlinarith
  · have hs' : slope ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have h := mul_nonpos_of_nonpos_of_nonneg hs' (sub_nonneg.mpr ht.1)
    nlinarith

theorem hasDerivAt_H (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt H (Real.log |u| + 1) u := by
  have hH : H = fun y : ℝ => y * Real.log y := by
    funext y
    simp only [H, Real.log_abs]
  rw [hH]
  simpa only [Real.log_abs] using! Real.hasDerivAt_mul_log hu

theorem hasDerivAt_affineH (r slope c m : ℝ) (hm : r + slope*m ≠ 0) :
    HasDerivAt (fun t : ℝ => c * H (r + slope*t))
      (c * ((Real.log |r + slope*m| + 1) * slope)) m := by
  have harg : HasDerivAt (fun t : ℝ => r + slope*t) slope m := by
    convert! (hasDerivAt_const m r).add ((hasDerivAt_id m).const_mul slope) using 1
    ring
  convert! ((hasDerivAt_H (r + slope*m) hm).comp m harg).const_mul c using 1

theorem hasDerivAt_affineH_midpoint (a b r slope c : ℝ)
    (hm : r + slope*((a+b)/2) ≠ 0) :
    HasDerivAt (fun t : ℝ => c * H (r + slope*t))
      (c * ((Real.log |r + slope*((a+b)/2)| + 1) * slope)) ((a+b)/2) :=
  hasDerivAt_affineH r slope c ((a+b)/2) hm

theorem H_cross_zero {u R : ℝ} (hu : |u| ≤ R) (hR : R ≤ 1/4) :
    |H u| ≤ -R * Real.log R := by
  simpa only [H, mulLogAbs] using! mulLogAbs_cross_zero hu hR

theorem affineH_cross_zero {r slope c t R : ℝ}
    (hu : |r + slope*t| ≤ R) (hR : R ≤ 1/4) :
    |c * H (r + slope*t)| ≤ |c| * (-R * Real.log R) := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (H_cross_zero hu hR) (abs_nonneg c)

end
end Li2Unified.Proofs.Potential.CompactAffine

#print axioms Li2Unified.Proofs.Potential.CompactAffine.H_convexOn_nonneg
#print axioms Li2Unified.Proofs.Potential.CompactAffine.H_concaveOn_nonpos
#print axioms Li2Unified.Proofs.Potential.CompactAffine.affineH_convex_nonneg
#print axioms Li2Unified.Proofs.Potential.CompactAffine.affineH_concave_nonpos
#print axioms Li2Unified.Proofs.Potential.CompactAffine.affineH_concave_nonneg
#print axioms Li2Unified.Proofs.Potential.CompactAffine.affineH_convex_nonpos
#print axioms Li2Unified.Proofs.Potential.CompactAffine.hasDerivAt_affineH
#print axioms Li2Unified.Proofs.Potential.CompactAffine.hasDerivAt_affineH_midpoint
#print axioms Li2Unified.Proofs.Potential.CompactAffine.affineH_cross_zero

end


end
