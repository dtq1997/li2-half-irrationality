module
public import Li2Unified.Modular.Positive.Packed.P096
public import Li2Unified.Modular.Positive.Packed.P179
public import Li2Unified.Modular.Base.OriginalContourIntegrable
public import Mathlib.MeasureTheory.Integral.Pi
public import Li2Unified.Modular.Positive.Packed.P105
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Li2Unified.Modular.Positive.Packed.P095

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf.LayerComparison

def starArmBase (b : Fin 3) (y : ℝ) : ℝ :=
  if b.val = 0 then Vray y else Vvertical y

/-- The centered coordinates are exactly the three axes used by `psiRay/Up/Down`. -/
theorem starArm_base_potential_eq (b : Fin 3) (y : ℝ) :
    starArmBase b y + 4*comparisonPotential (starAxisPoint (b,y)) =
      starArmPsi b y := by
  fin_cases b
  · simp [starArmBase, starArmPsi, starAxisPoint, point, psiRay]
  · simp [starArmBase, starArmPsi, starAxisPoint, point, psiUp]
  · simp [starArmBase, starArmPsi, starAxisPoint, point, psiDown]

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.starArm_base_potential_eq

end

section
open MeasureTheory Set
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

/-- Exact finite product integration on the actual three-arm product measure. -/
theorem star_pi_product (h : ℕ) (f : Fin 3 × ℝ → ℝ)
    (hf : Integrable f contourMeasure) :
    Integrable (fun v : Fin h → Fin 3 × ℝ => ∏ i, f (v i))
      (Measure.pi fun _ : Fin h => contourMeasure) ∧
    (∫ v : Fin h → Fin 3 × ℝ, (∏ i, f (v i))
      ∂(Measure.pi fun _ : Fin h => contourMeasure)) =
      (∫ z, f z ∂contourMeasure) ^ h := by
  haveI : SigmaFinite (volume.restrict (Ioi (0:ℝ))) :=
    Measure.sigmaFinite_of_le volume Measure.restrict_le_self
  haveI : SigmaFinite contourMeasure := by
    unfold contourMeasure
    infer_instance
  constructor
  · exact Integrable.fintype_prod (fun _ => hf)
  · simpa only [Fintype.card_fin] using!
      (integral_fintype_prod_eq_pow (ι := Fin h) (μ := contourMeasure) f)

/-- A fixed, integrable pointwise envelope for each rescaled star arm. -/
def starEnvelope (v : Fin 3 × ℝ) : ℝ :=
  Real.exp (9/5:ℝ) * ((1+|v.2|)^6 * Real.exp (-(1/10:ℝ)*|v.2|))

theorem starEnvelope_integrable : Integrable starEnvelope contourMeasure := by
  have hR : Integrable (fun y : ℝ =>
      Real.exp (9/5:ℝ) * ((1+|y|)^6 * Real.exp (-(1/10:ℝ)*|y|)))
      (volume.restrict (Ioi (0:ℝ))) :=
    ((Li2.original_integrable_one_add_abs_pow_exp 6
      (by norm_num : (0:ℝ)<1/10)).const_mul (Real.exp (9/5:ℝ))).integrableOn
  unfold contourMeasure
  exact hR.comp_snd Measure.count

theorem starEnvelope_nonneg (v : Fin 3 × ℝ) : 0 ≤ starEnvelope v := by
  unfold starEnvelope
  positivity

def starEnvelopeConstant : ℝ :=
  1 + ∫ z, starEnvelope z ∂contourMeasure

theorem starEnvelopeConstant_pos : 0 < starEnvelopeConstant := by
  have hnonneg : 0 ≤ ∫ z, starEnvelope z ∂contourMeasure :=
    integral_nonneg starEnvelope_nonneg
  unfold starEnvelopeConstant
  linarith

theorem star_envelope_product_integral (h n : ℕ) :
    Integrable (fun v : Fin h → Fin 3 × ℝ =>
      ∏ i, Real.exp ((n:ℝ)*(19/10:ℝ)) * starEnvelope (v i))
      (Measure.pi fun _ : Fin h => contourMeasure) ∧
    (∫ v : Fin h → Fin 3 × ℝ,
      (∏ i, Real.exp ((n:ℝ)*(19/10:ℝ)) * starEnvelope (v i))
      ∂(Measure.pi fun _ : Fin h => contourMeasure)) =
      (Real.exp ((n:ℝ)*(19/10:ℝ)) *
        (∫ z, starEnvelope z ∂contourMeasure)) ^ h := by
  have h := star_pi_product h
    (fun z => Real.exp ((n:ℝ)*(19/10:ℝ)) * starEnvelope z)
    (starEnvelope_integrable.const_mul _)
  simpa only [integral_const_mul] using! h

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.star_pi_product
#print axioms Li2Unified.Proofs.Arithmetic.starEnvelope_integrable
#print axioms Li2Unified.Proofs.Arithmetic.star_envelope_product_integral

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf.LayerComparison

/-- The weight and a compensating potential factor are bounded by one fixed
integrable envelope on every scaled arm. -/
theorem star_weight_potential_envelope (n : ℕ) (hn : 1 ≤ n)
    (b : Fin 3) (y : ℝ) (hy : 0 ≤ y) :
    (Li2.Sn n : ℝ) * ‖density b ((n:ℝ)*y) *
      Li2.originalComplexQuotient (4*n) ((Li2.D n)^3)
        (point b ((n:ℝ)*y))‖ ≤
      starPartitionWeightConstant * ((n:ℝ)+1)^12 *
        Real.exp (-4*(n:ℝ)*comparisonPotential (starAxisPoint (b,y))) *
        (Real.exp ((n:ℝ)*(19/10:ℝ))*starEnvelope (b,y)) := by
  have hw := star_weight_scaled n hn b y hy
  have he := starArm_exp_majorant n hn b y hy
  have hbase := starArm_base_potential_eq b y
  have hid : Real.exp ((n:ℝ)*starArmBase b y) =
      Real.exp (-4*(n:ℝ)*comparisonPotential (starAxisPoint (b,y))) *
        Real.exp ((n:ℝ)*starArmPsi b y) := by
    rw [← Real.exp_add]
    congr 1
    rw [← hbase]
    ring
  have hfac : 0 ≤ starPartitionWeightConstant * ((n:ℝ)+1)^12 *
      Real.exp (-4*(n:ℝ)*comparisonPotential (starAxisPoint (b,y))) := by
    have hC := starPartitionWeightConstant_pos
    positivity
  calc
    _ ≤ starPartitionWeightConstant * ((n:ℝ)+1)^12 * (1+y)^6 *
        Real.exp ((n:ℝ)*starArmBase b y) := by
          simpa only [starArmBase] using! hw
    _ = starPartitionWeightConstant * ((n:ℝ)+1)^12 *
        Real.exp (-4*(n:ℝ)*comparisonPotential (starAxisPoint (b,y))) *
        ((1+y)^6 * Real.exp ((n:ℝ)*starArmPsi b y)) := by
          rw [hid]
          ring
    _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hfac
          have hneg : -(1/10:ℝ)*|y| = -|y|/10 := by ring
          simpa only [starEnvelope, hneg] using! he

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_weight_potential_envelope

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section

/-- Multiply pointwise weight bounds against the exact potential exponential;
the position-dependent potential cancels before integration. -/
theorem star_product_potential_cancel (h : ℕ) (q A : ℝ)
    (hq : 0 < q)
    (w p g : Fin h → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hbound : ∀ i, q*w i ≤ A*Real.exp (-p i)*g i) :
    Real.exp (∑ i : Fin h, p i) * (∏ i : Fin h, w i) ≤
      (A/q)^h * (∏ i : Fin h, g i) := by
  have hsingle (i : Fin h) : w i * Real.exp (p i) ≤ (A/q)*g i := by
    have hmul := mul_le_mul_of_nonneg_right (hbound i) (Real.exp_pos (p i)).le
    have hcancel : Real.exp (-p i)*Real.exp (p i) = 1 := by
      rw [← Real.exp_add]
      simp
    have hqle : (w i * Real.exp (p i))*q ≤ A*g i := by
      calc
        (w i * Real.exp (p i))*q = (q*w i)*Real.exp (p i) := by ring
        _ ≤ (A*Real.exp (-p i)*g i)*Real.exp (p i) := hmul
        _ = A*(Real.exp (-p i)*Real.exp (p i))*g i := by ring
        _ = A*g i := by rw [hcancel]; ring
    calc
      _ ≤ (A*g i)/q := (le_div_iff₀ hq).mpr hqle
      _ = (A/q)*g i := by rw [div_mul_eq_mul_div]
  have hprod : (∏ i : Fin h, w i * Real.exp (p i)) ≤
      ∏ i : Fin h, (A/q)*g i := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact mul_nonneg (hw i) (Real.exp_pos _).le
    · intro i _
      exact hsingle i
  calc
    Real.exp (∑ i : Fin h, p i) * (∏ i : Fin h, w i) =
        ∏ i : Fin h, w i * Real.exp (p i) := by
          rw [Finset.prod_mul_distrib, ← Real.exp_sum]
          ring
    _ ≤ ∏ i : Fin h, (A/q)*g i := hprod
    _ = (A/q)^h * (∏ i : Fin h, g i) := by
          rw [Finset.prod_mul_distrib]
          rw [Finset.prod_const, Finset.card_fin]

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_product_potential_cancel

end

section
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf.LayerComparison

/-- The actual scaled partition density, with all position-dependent
comparison potentials canceled. The only unproved input is the independent
discrete energy inequality for distinct centers. -/
theorem starPartitionDensity_scaled_bound (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (2*n) → Fin 3 × ℝ)
    (hcoord : ∀ i : Fin (2*n), 0 ≤ (v i).2)
    (henergy : Function.Injective (fun i => starAxisPoint (v i)) →
      2 * (∑ i : Fin (2*n),
        ∑ j ∈ Finset.Ioi i,
          Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) ≤
        4*(n:ℝ) * (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
          4*(n:ℝ)^2 * comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :
    starPartitionDensity n
        (fun i => Proofs.Measure.starScale (n:ℝ) (v i)) ≤
      (n:ℝ)^((2*n)*(2*n-1)) *
        Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
        ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) *
        (∏ i : Fin (2*n),
          Real.exp ((n:ℝ)*(19/10:ℝ))*starEnvelope (v i)) := by
  let p : Fin (2*n) → ℝ := fun i =>
    4*(n:ℝ)*comparisonPotential (starAxisPoint (v i))
  let w : Fin (2*n) → ℝ := fun i =>
    ‖density (v i).1 ((n:ℝ)*(v i).2) *
      Li2.originalComplexQuotient (4*n) ((Li2.D n)^3)
        (point (v i).1 ((n:ℝ)*(v i).2))‖
  let g : Fin (2*n) → ℝ := fun i =>
    Real.exp ((n:ℝ)*(19/10:ℝ))*starEnvelope (v i)
  let A : ℝ := starPartitionWeightConstant*((n:ℝ)+1)^12
  let T : ℝ := -4*(n:ℝ)^2*comparisonEnergy +
    2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)
  have hSn : 0 < (Li2.Sn n:ℝ) := by exact_mod_cast Li2.Sn_pos n
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact norm_nonneg _
  have hbound : ∀ i, (Li2.Sn n:ℝ)*w i ≤ A*Real.exp (-p i)*g i := by
    intro i
    have h := star_weight_potential_envelope n hn (v i).1 (v i).2 (hcoord i)
    have hpair : ((v i).1, (v i).2) = v i := Prod.mk.eta
    rw [hpair] at h
    have hneg : -4*(n:ℝ)*comparisonPotential (starAxisPoint (v i)) =
        -(4*(n:ℝ)*comparisonPotential (starAxisPoint (v i))) := by ring
    rw [hneg] at h
    simpa only [p, w, g, A] using! h
  have hproduct := star_product_potential_cancel (2*n) (Li2.Sn n:ℝ) A
    hSn w p g hw hbound
  have hdet := star_vandermonde_original_energy n hn v henergy
  have hsum : (∑ i : Fin (2*n), p i) =
      4*(n:ℝ)*(∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) := by
    dsimp [p]
    rw [Finset.mul_sum]
  have hexp : Real.exp (4*(n:ℝ)*
      (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
        4*(n:ℝ)^2*comparisonEnergy +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) =
      Real.exp (∑ i : Fin (2*n), p i)*Real.exp T := by
    rw [← Real.exp_add]
    congr 1
    rw [hsum]
    dsimp [T]
    ring
  rw [hexp] at hdet
  have hprodnonneg : 0 ≤ ∏ i : Fin (2*n), w i := by
    exact Finset.prod_nonneg (fun i _ => hw i)
  calc
    starPartitionDensity n (fun i => Proofs.Measure.starScale (n:ℝ) (v i)) =
        ‖(Matrix.of fun i j : Fin (2*n) =>
          point (v j).1 ((n:ℝ)*(v j).2)^i.val).det‖^2 *
          (∏ i : Fin (2*n), w i) := by
            rfl
    _ ≤ (n:ℝ)^((2*n)*(2*n-1)) *
          (Real.exp (∑ i : Fin (2*n), p i)*Real.exp T) *
          (∏ i : Fin (2*n), w i) :=
            mul_le_mul_of_nonneg_right hdet hprodnonneg
    _ = (n:ℝ)^((2*n)*(2*n-1)) * Real.exp T *
          (Real.exp (∑ i : Fin (2*n), p i) *
            (∏ i : Fin (2*n), w i)) := by ring
    _ ≤ (n:ℝ)^((2*n)*(2*n-1)) * Real.exp T *
          ((A/(Li2.Sn n:ℝ))^(2*n) * (∏ i : Fin (2*n), g i)) :=
            mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = _ := by
      dsimp [A, T, g]
      ring

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.starPartitionDensity_scaled_bound

end

section
open MeasureTheory Set
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic

/-- Every coordinate of the actual product contour lies on a nonnegative arm,
almost everywhere. -/
theorem star_pi_coordinates_nonneg (h : ℕ) :
    ∀ᵐ v : Fin h → Fin 3 × ℝ
      ∂(Measure.pi fun _ : Fin h => contourMeasure),
      ∀ i : Fin h, 0 ≤ (v i).2 := by
  haveI : SigmaFinite (volume.restrict (Ioi (0:ℝ))) :=
    Measure.sigmaFinite_of_le volume Measure.restrict_le_self
  haveI : SigmaFinite contourMeasure := by
    unfold contourMeasure
    infer_instance
  have hone : ∀ᵐ z : Fin 3 × ℝ ∂contourMeasure, 0 ≤ z.2 := by
    unfold contourMeasure
    have hm : MeasurableSet {z : Fin 3 × ℝ | 0 ≤ z.2} := by
      change MeasurableSet (Prod.snd ⁻¹' Ici (0:ℝ))
      exact measurableSet_Ici.preimage measurable_snd
    apply (Measure.ae_prod_iff_ae_ae hm).2
    filter_upwards [] with b
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact hy.le
  exact Filter.eventually_all.2 (fun i : Fin h =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin h => contourMeasure)).eventually hone)

/-- Integrability of the exact partition density survives the finite-product
scaling change of variables. -/
theorem starPartitionDensity_scaled_integrable (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun v : Fin (2*n) → Fin 3 × ℝ =>
      starPartitionDensity n
        (fun i => Proofs.Measure.starScale (n:ℝ) (v i)))
      (Measure.pi fun _ : Fin (2*n) => contourMeasure) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hf : Integrable (starPartitionDensity n)
      (Measure.pi fun _ : Fin (2*n) => contourMeasure) := by
    simpa only [starPartitionDensity] using! Proofs.Contour.star_partition_integrable n
  have hm : Measurable (fun v : Fin (2*n) → Fin 3 × ℝ =>
      fun i => Proofs.Measure.starScale (n:ℝ) (v i)) := by
    unfold Proofs.Measure.starScale
    fun_prop
  have hmap : Integrable (starPartitionDensity n)
      (Measure.map (fun v : Fin (2*n) → Fin 3 × ℝ =>
        fun i => Proofs.Measure.starScale (n:ℝ) (v i))
        (Measure.pi fun _ : Fin (2*n) => contourMeasure)) := by
    rw [Proofs.Measure.starScale_pi_map (2*n) (n:ℝ) hnpos]
    exact hf.smul_measure (by simp)
  exact (integrable_map_measure hmap.aestronglyMeasurable hm.aemeasurable).mp hmap

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_pi_coordinates_nonneg
#print axioms Li2Unified.Proofs.Arithmetic.starPartitionDensity_scaled_integrable

end

section
open MeasureTheory Filter
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HalfAnalytic
open Li2Unified.Instances.PosHalf.LayerComparison

/-- Actual star partition upper bound at every positive `n`. Its sole independent
analytic input is the distinct-center discrete energy inequality; compact
one-body leaf bounds remain visible in the axiom audit until discharged. -/
theorem starPartition_explicit_bound (n : ℕ) (hn : 1 ≤ n)
    (henergy : ∀ v : Fin (2*n) → Fin 3 × ℝ,
      Function.Injective (fun i => starAxisPoint (v i)) →
        2 * (∑ i : Fin (2*n),
          ∑ j ∈ Finset.Ioi i,
            Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) ≤
          4*(n:ℝ) * (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
            4*(n:ℝ)^2 * comparisonEnergy +
            2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :
    starPartition n ≤
      (n:ℝ)^((2*n)^2) *
        Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
        ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) *
        (Real.exp ((n:ℝ)*(19/10:ℝ)) *
          (∫ z, starEnvelope z ∂contourMeasure))^(2*n) := by
  let B : ℝ := (n:ℝ)^((2*n)*(2*n-1)) *
    Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
      2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
    ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n)
  have hfactor := star_envelope_product_integral (2*n) n
  have hleft := starPartitionDensity_scaled_integrable n hn
  have hright : Integrable (fun v : Fin (2*n) → Fin 3 × ℝ =>
      B * (∏ i : Fin (2*n),
        Real.exp ((n:ℝ)*(19/10:ℝ))*starEnvelope (v i)))
      (Measure.pi fun _ : Fin (2*n) => contourMeasure) :=
    hfactor.1.const_mul B
  have hpoint : ∀ᵐ v : Fin (2*n) → Fin 3 × ℝ
      ∂(Measure.pi fun _ : Fin (2*n) => contourMeasure),
      starPartitionDensity n
        (fun i => Proofs.Measure.starScale (n:ℝ) (v i)) ≤
        B * (∏ i : Fin (2*n),
          Real.exp ((n:ℝ)*(19/10:ℝ))*starEnvelope (v i)) := by
    filter_upwards [star_pi_coordinates_nonneg (2*n)] with v hv
    simpa only [B] using!
      starPartitionDensity_scaled_bound n hn v hv (henergy v)
  have hint : (∫ v : Fin (2*n) → Fin 3 × ℝ,
      starPartitionDensity n
        (fun i => Proofs.Measure.starScale (n:ℝ) (v i))
      ∂(Measure.pi fun _ : Fin (2*n) => contourMeasure)) ≤
      B * (Real.exp ((n:ℝ)*(19/10:ℝ)) *
        (∫ z, starEnvelope z ∂contourMeasure))^(2*n) := by
    have h := integral_mono_ae hleft hright hpoint
    rw [integral_const_mul, hfactor.2] at h
    exact h
  have hnnonneg : 0 ≤ (n:ℝ)^(2*n) := by positivity
  have hcount : (2*n)+(2*n)*(2*n-1) = (2*n)^2 := by
    have hh : 1 ≤ 2*n := by omega
    calc
      (2*n)+(2*n)*(2*n-1) = (2*n)*((2*n-1)+1) := by ring
      _ = (2*n)*(2*n) := by rw [Nat.sub_add_cancel hh]
      _ = (2*n)^2 := by ring
  calc
    starPartition n = (n:ℝ)^(2*n) *
      (∫ v : Fin (2*n) → Fin 3 × ℝ,
        starPartitionDensity n
          (fun i => Proofs.Measure.starScale (n:ℝ) (v i))
        ∂(Measure.pi fun _ : Fin (2*n) => contourMeasure)) :=
          starPartition_scaled n hn
    _ ≤ (n:ℝ)^(2*n) *
      (B * (Real.exp ((n:ℝ)*(19/10:ℝ)) *
        (∫ z, starEnvelope z ∂contourMeasure))^(2*n)) :=
          mul_le_mul_of_nonneg_left hint hnnonneg
    _ = _ := by
      dsimp [B]
      rw [show (n:ℝ)^(2*n) *
          ((n:ℝ)^((2*n)*(2*n-1)) *
            Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
              2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
            ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) *
            (Real.exp ((n:ℝ)*(19/10:ℝ)) *
              (∫ z, starEnvelope z ∂contourMeasure))^(2*n)) =
          ((n:ℝ)^(2*n)*(n:ℝ)^((2*n)*(2*n-1))) *
            Real.exp (-4*(n:ℝ)^2*comparisonEnergy +
              2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) *
            ((starPartitionWeightConstant*((n:ℝ)+1)^12)/(Li2.Sn n:ℝ))^(2*n) *
            (Real.exp ((n:ℝ)*(19/10:ℝ)) *
              (∫ z, starEnvelope z ∂contourMeasure))^(2*n) by ring]
      rw [← pow_add, hcount]

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.starPartition_explicit_bound

end


end
