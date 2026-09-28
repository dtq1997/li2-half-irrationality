module
public import Li2Unified.Modular.Positive.Packed.P096
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Li2Unified.Modular.Positive.Packed.P104
public import Li2Unified.Modular.Positive.Packed.P181
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Instances.PosHalf.LayerComparison

/-- Specialize the arbitrary-center discrete energy theorem at `h=2n` and
circle radius `ε=1/(2n)`. This checks the exact finite error constants needed
by the actual partition bound. -/
theorem star_discrete_energy_specialize (n : ℕ) (hn : 1 ≤ n)
    (v : Fin (2*n) → Fin 3 × ℝ)
    (hgeneral : ∀ (h : ℕ), 0 < h → ∀ (x : Fin h → ℂ),
      Function.Injective x → ∀ (ε : ℝ), 0 < ε →
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j - x i‖) ≤
        2*(h:ℝ)*(∑ i : Fin h, comparisonPotential (x i)) -
          (h:ℝ)^2*comparisonEnergy - (h:ℝ)*Real.log ε +
          (11/5:ℝ)*(h:ℝ)^2*ε)
    (hinj : Function.Injective (fun i => starAxisPoint (v i))) :
    2 * (∑ i : Fin (2*n),
      ∑ j ∈ Finset.Ioi i,
        Real.log ‖starAxisPoint (v j) - starAxisPoint (v i)‖) ≤
      4*(n:ℝ)*(∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
        4*(n:ℝ)^2*comparisonEnergy +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have heps : (0:ℝ) < 1/(2*(n:ℝ)) := by positivity
  have hlog : Real.log (1/(2*(n:ℝ))) = -Real.log (2*(n:ℝ)) := by
    rw [one_div, Real.log_inv]
  have h := hgeneral (2*n) (by omega)
    (fun i => starAxisPoint (v i)) hinj (1/(2*(n:ℝ))) heps
  have hR :
      2*((2*n:ℕ):ℝ)*
          (∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
        ((2*n:ℕ):ℝ)^2*comparisonEnergy -
        ((2*n:ℕ):ℝ)*Real.log (1/(2*(n:ℝ))) +
        (11/5:ℝ)*((2*n:ℕ):ℝ)^2*(1/(2*(n:ℝ))) =
      4*(n:ℝ)*(∑ i : Fin (2*n), comparisonPotential (starAxisPoint (v i))) -
        4*(n:ℝ)^2*comparisonEnergy +
        2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ) := by
    push_cast
    rw [hlog]
    field_simp
    ring
  exact hR ▸ h

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_discrete_energy_specialize

end

section
namespace Li2Unified.Proofs.Arithmetic
open Filter Topology
noncomputable section

/-- Absorb only subquadratic factors. No fixed quadratic margin is spent. -/
theorem star_final_prefactor_eventually (C I S ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      starPartitionPrefactor n * C ^ (2*n) *
        Real.exp ((-4*I+2*S)*(n:ℝ)^2 +
          12*(n:ℝ)*Real.log ((n:ℝ)+1) +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) ≤
      Real.exp ((6-4*Real.log 2-4*I+2*S+ε)*(n:ℝ)^2) := by
  let K := starPartitionErrorConstant + 32 + 4*|Real.log C|
  filter_upwards [star_n_log_eventually_le_square K hε,
    eventually_ge_atTop (1:ℕ)] with n herr hn
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hL : (1/2:ℝ) ≤ Real.log ((n:ℝ)+1) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have hm := Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show (2:ℝ)≤(n:ℝ)+1 by linarith)
    norm_num at h2
    linarith
  have hLn := Real.log_le_log (by positivity : (0:ℝ)<2*(n:ℝ))
    (show 2*(n:ℝ)≤((n:ℝ)+1)^2 by nlinarith [sq_nonneg (n:ℝ)])
  rw [Real.log_pow] at hLn
  norm_num only [Nat.cast_ofNat] at hLn
  have hlogC : 2*(n:ℝ)*Real.log C ≤
      4*|Real.log C| *(n:ℝ)*Real.log ((n:ℝ)+1) := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log C))
      (by positivity : (0:ℝ)≤2*(n:ℝ))
    have h2 := mul_le_mul_of_nonneg_left hL
      (by positivity : (0:ℝ)≤4*|Real.log C| *(n:ℝ))
    nlinarith only [h1,h2]
  have hlogn := mul_le_mul_of_nonneg_left hLn
    (by positivity : (0:ℝ)≤2*(n:ℝ))
  have hlinear := mul_le_mul_of_nonneg_left hL
    (by positivity : (0:ℝ)≤(44/5:ℝ)*(n:ℝ))
  have hslack : 0 ≤ (n:ℝ)*Real.log ((n:ℝ)+1) := by positivity
  have hpow : C^(2*n) = Real.exp (2*(n:ℝ)*Real.log C) := by
    have h := Real.exp_log (pow_pos hC (2*n))
    rw [Real.log_pow] at h
    push_cast at h
    exact h.symm
  have hp := starPartitionPrefactor_le_exp n hn
  calc
    _ ≤ Real.exp ((6-4*Real.log 2)*(n:ℝ)^2 +
        starPartitionErrorConstant*(n:ℝ)*Real.log ((n:ℝ)+1)) * C^(2*n) *
        Real.exp ((-4*I+2*S)*(n:ℝ)^2 +
          12*(n:ℝ)*Real.log ((n:ℝ)+1) +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp (pow_nonneg hC.le _)) (Real.exp_pos _).le
    _ = Real.exp (((6-4*Real.log 2)*(n:ℝ)^2 +
        starPartitionErrorConstant*(n:ℝ)*Real.log ((n:ℝ)+1)) +
        2*(n:ℝ)*Real.log C + ((-4*I+2*S)*(n:ℝ)^2 +
          12*(n:ℝ)*Real.log ((n:ℝ)+1) +
          2*(n:ℝ)*Real.log (2*(n:ℝ)) + (22/5:ℝ)*(n:ℝ))) := by
      rw [hpow, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      dsimp [K] at herr
      nlinarith only [herr,hlogC,hlogn,hlinear,hslack]

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_final_prefactor_eventually

end

section
open Polynomial Filter
open scoped BigOperators
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Instances.PosHalf.LayerComparison

/-- The energy-bridge conclusion follows from the one independent
distinct-center discrete logarithmic energy theorem. -/
theorem star_actual_energy_bridge_of_discrete_energy
    (hgeneral : ∀ (h : ℕ), 0 < h → ∀ (x : Fin h → ℂ),
      Function.Injective x → ∀ (δ : ℝ), 0 < δ →
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j - x i‖) ≤
        2*(h:ℝ)*(∑ i : Fin h, comparisonPotential (x i)) -
          (h:ℝ)^2*comparisonEnergy - (h:ℝ)*Real.log δ +
          (11/5:ℝ)*(h:ℝ)^2*δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |aeval Li2Unified.Instances.PosHalf.value
          (Li2Unified.Instances.PosHalf.Qtilde n)| ≤
        Real.exp ((6-4*Real.log 2-4*comparisonEnergy+
          2*(19/10:ℝ)+ε)*(n:ℝ)^2) := by
  intro ε hε
  filter_upwards
    [star_final_prefactor_eventually starEnvelopeConstant comparisonEnergy
      (19/10:ℝ) ε starEnvelopeConstant_pos hε,
     eventually_ge_atTop (1:ℕ)] with n hfinal hn
  exact (star_Qtilde_bound_of_discrete_energy n hn
    (fun v => star_discrete_energy_specialize n hn v hgeneral)).trans hfinal

end
end Li2Unified.Proofs.Arithmetic
#print axioms Li2Unified.Proofs.Arithmetic.star_actual_energy_bridge_of_discrete_energy

end

section
/-! Globally bounded curve representation for a finite straight cell.
Only geometry and mass normalization are paid here. Equality to a density
measure and logarithmic integrability remain separate obligations. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "SegmentCurve: imports loaded"
  out.flush

def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clampUnit_mem (x : ℝ) : clampUnit x ∈ Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clampUnit_eq_of_mem {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : clampUnit x = x := by
  simp only [clampUnit, min_eq_right hx.2, max_eq_right hx.1]

lemma continuous_clampUnit : Continuous clampUnit := by
  unfold clampUnit
  fun_prop

def segmentCurve (a b : ℂ) (θ : ℝ) : ℂ :=
  (1-clampUnit (θ/(2*Real.pi))) • a + clampUnit (θ/(2*Real.pi)) • b

lemma continuous_segmentCurve (a b : ℂ) : Continuous (segmentCurve a b) := by
  have ht : Continuous (fun θ : ℝ => clampUnit (θ/(2*Real.pi))) :=
    continuous_clampUnit.comp (continuous_id.div_const _)
  simpa only [segmentCurve, Complex.real_smul] using!
    ((Complex.continuous_ofReal.comp (continuous_const.sub ht)).mul continuous_const).add
      ((Complex.continuous_ofReal.comp ht).mul continuous_const)

lemma segmentCurve_on (a b : ℂ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2*Real.pi)) :
    segmentCurve a b θ = (1-θ/(2*Real.pi)) • a + (θ/(2*Real.pi)) • b := by
  have hp : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have ht : θ/(2*Real.pi) ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hθ.1 hp.le, (div_le_one hp).mpr hθ.2⟩
  simp only [segmentCurve, clampUnit_eq_of_mem ht]

lemma segmentCurve_norm_le (a b : ℂ) (θ : ℝ) :
    ‖segmentCurve a b θ‖ ≤ max ‖a‖ ‖b‖ := by
  let t := clampUnit (θ/(2*Real.pi))
  have ht : 0 ≤ t ∧ t ≤ 1 := clampUnit_mem _
  calc
    ‖segmentCurve a b θ‖ ≤ ‖(1-t) • a‖ + ‖t • b‖ := norm_add_le _ _
    _ = (1-t)*‖a‖ + t*‖b‖ := by
      rw [Complex.real_smul, Complex.real_smul, norm_mul, norm_mul,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1-t), abs_of_nonneg ht.1]
    _ ≤ (1-t)*max ‖a‖ ‖b‖ + t*max ‖a‖ ‖b‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
    _ = max ‖a‖ ‖b‖ := by ring

#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "SegmentCurve: declarations processed"
  out.flush

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Exact angular-to-interval density normalization.
This uses total interval integrals, so it does not assert integrability.
Actual log-kernel integrability remains a separate theorem. -/
open MeasureTheory
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

lemma angular_density_integral (f : ℝ → ℝ) (a b density : ℝ) :
    (density*(b-a)/(2*Real.pi)) *
      (∫ θ in (0:ℝ)..2*Real.pi, f (((b-a)/(2*Real.pi))*θ+a)) =
        density * ∫ x in a..b, f x := by
  have hb : ((b-a)/(2*Real.pi))*(2*Real.pi)+a = b := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  have h := intervalIntegral.smul_integral_comp_mul_add
    (a := (0:ℝ)) (b := 2*Real.pi) f ((b-a)/(2*Real.pi)) a
  simp only [smul_eq_mul, mul_zero, zero_add, hb] at h
  calc
    _ = density * (((b-a)/(2*Real.pi)) *
      (∫ θ in (0:ℝ)..2*Real.pi, f (((b-a)/(2*Real.pi))*θ+a))) := by ring
    _ = _ := congrArg (fun x : ℝ => density*x) h

end
end Li2Unified.ParameterFamily.Energy

end

end
