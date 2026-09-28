module
public import Li2Unified.Modular.Positive.Packed.P069
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Positive.Packed.P071
public import Li2Unified.Modular.Positive.Packed.P072
public import Li2Unified.Modular.Base.OriginalContourRational
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial MeasureTheory Filter Set
open scoped BigOperators
namespace Li2Unified.Stage0.HalfAnalytic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Instances.PosHalf.LayerComparison

def point (b : Fin 3) (t : ℝ) : ℂ :=
  if b.val = 0 then ((1/2+t:ℝ):ℂ)
  else if b.val = 1 then (1/2:ℂ)+(t:ℂ)*Complex.I
  else (1/2:ℂ)-(t:ℂ)*Complex.I

def power (z : ℂ) : ℂ := Complex.exp ((Real.log (1/2:ℝ):ℂ)*z)
def kappaPlus (z : ℂ) : ℂ := 1/(1-Complex.exp (-(2*(Real.pi:ℂ)*Complex.I)*z))
def kappaMinus (z : ℂ) : ℂ := 1/(1-Complex.exp ((2*(Real.pi:ℂ)*Complex.I)*z))

def density (b : Fin 3) (t : ℝ) : ℂ :=
  let z := point b t
  if b.val = 0 then (Real.log 2:ℂ)*z*power z
  else if b.val = 1 then Complex.I*z*deriv (fun w => power w*kappaPlus w) z
  else -Complex.I*z*deriv (fun w => power w*kappaMinus w) z

def contourMeasure : Measure (Fin 3 × ℝ) :=
  (Measure.count : Measure (Fin 3)).prod (volume.restrict (Ioi (0:ℝ)))

def starMoment (m : ℕ) (F : ℚ[X]) : ℂ :=
  ∫ v : Fin 3 × ℝ, density v.1 v.2 *
    Li2.originalComplexQuotient m F (point v.1 v.2) ∂contourMeasure


def starPartition (n : ℕ) : ℝ :=
  ∫ v : Fin (2*n) → (Fin 3 × ℝ),
    ‖(Matrix.of fun i j : Fin (2*n) => (point (v j).1 (v j).2)^i.val).det‖^2 *
      (∏ i : Fin (2*n), ‖density (v i).1 (v i).2 *
        Li2.originalComplexQuotient (4*n) ((Li2.D n)^3) (point (v i).1 (v i).2)‖)
    ∂(Measure.pi fun _ : Fin (2*n) => contourMeasure)


def baseRay (x : ℝ) : ℝ :=
  4*Real.log 4-1 + 3*(∫ t in (0:ℝ)..1, Real.log (t+x)) -
    (∫ t in (0:ℝ)..4, Real.log (t+x))
def baseVertical (y : ℝ) : ℝ :=
  4*Real.log 4-1 + 3*(∫ t in (0:ℝ)..1, Real.log ‖(t:ℂ)+(y:ℂ)*Complex.I‖) -
    (∫ t in (0:ℝ)..4, Real.log ‖(t:ℂ)+(y:ℂ)*Complex.I‖)
def Vray (x : ℝ) : ℝ := baseRay x-x*Real.log 2
def Vvertical (y : ℝ) : ℝ := baseVertical y-2*Real.pi*|y|
def psiRay (x : ℝ) : ℝ := Vray x+4*comparisonPotential (x:ℂ)
def psiUp (y : ℝ) : ℝ := Vvertical y+4*comparisonPotential ((y:ℂ)*Complex.I)
def psiDown (y : ℝ) : ℝ := Vvertical y+4*comparisonPotential (-(y:ℂ)*Complex.I)

end
end Li2Unified.Stage0.HalfAnalytic

end

section
open MeasureTheory Set
open scoped BigOperators
namespace Li2Unified.Proofs.Measure
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

def starScale (c : ℝ) (v : Fin 3 × ℝ) : Fin 3 × ℝ := (v.1,c*v.2)

lemma positiveRay_map_mul (c : ℝ) (hc : 0 < c) :
    Measure.map (fun x : ℝ => c*x) (volume.restrict (Ioi 0)) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Ioi 0) := by
  have hpre : (fun x : ℝ => c*x) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi]
    exact mul_pos_iff_of_pos_left hc
  have h := Measure.restrict_map (measurable_const_mul c) (s := Ioi (0:ℝ)) measurableSet_Ioi
    (μ := (volume : Measure ℝ))
  rw [hpre, Real.map_volume_mul_left hc.ne', Measure.restrict_smul,
    abs_of_pos (inv_pos.mpr hc)] at h
  exact h.symm

theorem starScale_map (c : ℝ) (hc : 0 < c) :
    Measure.map (starScale c) contourMeasure = ENNReal.ofReal c⁻¹ • contourMeasure := by
  have hm : starScale c = Prod.map id (fun x : ℝ => c*x) := rfl
  rw [hm, contourMeasure, ← Measure.map_prod_map _ _ measurable_id (measurable_const_mul c),
    Measure.map_id, positiveRay_map_mul c hc, Measure.prod_smul_right]


theorem starScale_pi_map (h : ℕ) (c : ℝ) (hc : 0 < c) :
    Measure.map (fun v : Fin h → Fin 3 × ℝ => fun i => starScale c (v i))
      (Measure.pi fun _ : Fin h => contourMeasure) =
      (ENNReal.ofReal c⁻¹)^h • (Measure.pi fun _ : Fin h => contourMeasure) := by
  have hm : Measurable (starScale c) := by unfold starScale; fun_prop
  haveI : SigmaFinite contourMeasure := by
    unfold contourMeasure
    infer_instance
  haveI : SigmaFinite (ENNReal.ofReal c⁻¹ • contourMeasure) := by
    change SigmaFinite ((Real.toNNReal c⁻¹) • contourMeasure)
    infer_instance
  haveI : SigmaFinite (Measure.map (starScale c) contourMeasure) := by
    rw [starScale_map c hc]
    infer_instance
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  simp_rw [starScale_map c hc]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem integral_starScale_pi (h : ℕ) (c : ℝ) (hc : 0 < c)
    (f : (Fin h → Fin 3 × ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, f v ∂(Measure.pi fun _ : Fin h => contourMeasure)) =
      c^h * (∫ v, f (fun i => starScale c (v i))
        ∂(Measure.pi fun _ : Fin h => contourMeasure)) := by
  have hm : Measurable (fun v : Fin h → Fin 3 × ℝ => fun i => starScale c (v i)) := by
    unfold starScale
    fun_prop
  have hi := integral_map hm.aemeasurable hf.aestronglyMeasurable
    (μ := Measure.pi fun _ : Fin h => contourMeasure)
  rw [starScale_pi_map h c hc, integral_smul_measure] at hi
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le),
    smul_eq_mul] at hi
  rw [← hi, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, one_mul]

end
end Li2Unified.Proofs.Measure
#print axioms Li2Unified.Proofs.Measure.positiveRay_map_mul
#print axioms Li2Unified.Proofs.Measure.starScale_map

#print axioms Li2Unified.Proofs.Measure.integral_starScale_pi

end

section
/-! Algebraic bridge between the positive-half star kernels and the older
negative-half sine kernel. The analytic contour and limiting arguments are
separate obligations. -/

namespace Li2Unified.Proofs.Contour
noncomputable section

open Li2Unified.Stage0.HalfAnalytic

private def phase (z : ℂ) : ℂ := (Real.pi : ℂ) * Complex.I * z

private lemma sin_phase (z : ℂ) :
    2 * Complex.I * Complex.sin ((Real.pi : ℂ) * z) =
      Complex.exp (phase z) - Complex.exp (-phase z) := by
  unfold phase
  change 2 * Complex.I *
      ((Complex.exp (-((Real.pi : ℂ) * z) * Complex.I) -
        Complex.exp (((Real.pi : ℂ) * z) * Complex.I)) * Complex.I / 2) = _
  have hneg : -((Real.pi : ℂ) * z) * Complex.I =
      -((Real.pi : ℂ) * Complex.I * z) := by ring
  rw [hneg]
  have hpos : (Real.pi : ℂ) * z * Complex.I =
      (Real.pi : ℂ) * Complex.I * z := by ring
  rw [hpos]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma power_eq_original (z : ℂ) : power z = Li2.originalContourPower z := by
  unfold power Li2.originalContourPower
  have hlog : Real.log (1/2:ℝ) = -Real.log 2 := by
    simp [one_div, Real.log_inv]
  rw [hlog]
  congr 1
  push_cast
  ring

lemma point_up (t : ℝ) : point ⟨1, by decide⟩ t = Li2.originalContourPoint t := by
  simp [point, Li2.originalContourPoint]

lemma point_down (t : ℝ) : point ⟨2, by decide⟩ t = Li2.originalContourPoint (-t) := by
  simp [point, Li2.originalContourPoint]
  ring

lemma point_ray (t : ℝ) : point ⟨0, by decide⟩ t = ((1/2+t : ℝ) : ℂ) := by
  simp [point]

private lemma kappaPlus_phase (z : ℂ) :
    kappaPlus z = 1 / (1 - Complex.exp (-2 * phase z)) := by
  unfold kappaPlus phase
  congr 1
  ring

private lemma kappaMinus_phase (z : ℂ) :
    kappaMinus z = 1 / (1 - Complex.exp (2 * phase z)) := by
  unfold kappaMinus phase
  congr 1
  ring

private lemma exp_phase_sub (z : ℂ) :
    (1 - Complex.exp (-2 * phase z)) * Complex.exp (phase z) =
      Complex.exp (phase z) - Complex.exp (-phase z) := by
  have h : Complex.exp (-2 * phase z) * Complex.exp (phase z) =
      Complex.exp (-phase z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = Complex.exp (phase z) -
        Complex.exp (-2 * phase z) * Complex.exp (phase z) := by ring
    _ = _ := by rw [h]

private lemma exp_phase_sub_ne (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    Complex.exp (phase z) - Complex.exp (-phase z) ≠ 0 := by
  rw [← sin_phase]
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hz

private lemma plus_den_ne (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    1 - Complex.exp (-2 * phase z) ≠ 0 := by
  intro h
  apply exp_phase_sub_ne z hz
  rw [← exp_phase_sub, h, zero_mul]

private lemma minus_den_ne (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    1 - Complex.exp (2 * phase z) ≠ 0 := by
  intro h
  apply exp_phase_sub_ne z hz
  have he : Complex.exp (2 * phase z) * Complex.exp (-phase z) =
      Complex.exp (phase z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (phase z) - Complex.exp (-phase z) =
        -(1 - Complex.exp (2 * phase z)) * Complex.exp (-phase z) := by
      rw [← he]
      ring
    _ = 0 := by rw [h]; ring

lemma kappaPlus_eq_kernel (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    power z * kappaPlus z =
      Complex.exp (phase z) / (2 * (Real.pi : ℂ) * Complex.I) *
        Li2.originalContourKernel z := by
  rw [kappaPlus_phase, Li2.originalContourKernel, ← power_eq_original]
  have hden := plus_den_ne z hz
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hden, hz, hpi, Complex.I_ne_zero]
  rw [show power z * 2 * Complex.I * Complex.sin ((Real.pi : ℂ) * z) =
      power z * (2 * Complex.I * Complex.sin ((Real.pi : ℂ) * z)) by ring]
  rw [sin_phase, ← exp_phase_sub]
  rw [show -(2 * phase z) = -2 * phase z by ring]
  apply (div_eq_iff hden).2
  ring

lemma kappaMinus_eq_kernel (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    power z * kappaMinus z =
      -Complex.exp (-phase z) / (2 * (Real.pi : ℂ) * Complex.I) *
        Li2.originalContourKernel z := by
  rw [kappaMinus_phase, Li2.originalContourKernel, ← power_eq_original]
  have hden := minus_den_ne z hz
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hden, hz, hpi, Complex.I_ne_zero]
  rw [show power z * 2 * Complex.I * Complex.sin ((Real.pi : ℂ) * z) =
      power z * (2 * Complex.I * Complex.sin ((Real.pi : ℂ) * z)) by ring]
  rw [sin_phase]
  have he : Complex.exp (2 * phase z) * Complex.exp (-phase z) =
      Complex.exp (phase z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [← he]
  ring

lemma kappa_sum (z : ℂ)
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    kappaPlus z + kappaMinus z = 1 := by
  rw [kappaPlus_phase, kappaMinus_phase]
  have he : Complex.exp (-2 * phase z) =
      (Complex.exp (2 * phase z))⁻¹ := by
    convert Complex.exp_neg (2 * phase z) using 1
    ring
  have hp := plus_den_ne z hz
  have hm := minus_den_ne z hz
  rw [he] at hp ⊢
  have he0 : Complex.exp (2 * phase z) ≠ 0 := Complex.exp_ne_zero _
  have hEm : -1 + Complex.exp (2 * phase z) ≠ 0 := by
    intro h
    apply hm
    calc
      1 - Complex.exp (2 * phase z) =
          -(-1 + Complex.exp (2 * phase z)) := by ring
      _ = 0 := by rw [h]; ring
  have hEm' : Complex.exp (2 * phase z) - 1 ≠ 0 := by
    simpa only [sub_eq_add_neg, add_comm] using! hEm
  field_simp [hp, hm, he0, hEm]
  field_simp [hEm']
  ring

lemma kappaPlus_half : kappaPlus (1/2:ℂ) = 1/2 := by
  rw [kappaPlus_phase]
  have hphase : -2 * phase (1/2:ℂ) = -((Real.pi:ℂ) * Complex.I) := by
    unfold phase
    ring
  rw [hphase, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

lemma kappaMinus_half : kappaMinus (1/2:ℂ) = 1/2 := by
  rw [kappaMinus_phase]
  have hphase : 2 * phase (1/2:ℂ) = (Real.pi:ℂ) * Complex.I := by
    unfold phase
    ring
  rw [hphase, Complex.exp_pi_mul_I]
  norm_num

lemma endpoint_balance :
    -(1:ℂ) + kappaPlus (1/2:ℂ) + kappaMinus (1/2:ℂ) = 0 := by
  rw [kappaPlus_half, kappaMinus_half]
  ring

end
end Li2Unified.Proofs.Contour

end


end
