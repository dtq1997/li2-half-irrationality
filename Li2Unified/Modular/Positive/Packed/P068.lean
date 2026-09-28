module
public import Li2Unified.Modular.Positive.Packed.P036
public import Li2Unified.Modular.Base.PrimeObstruction
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Data.Finset.Lattice.Fold
public import Li2Unified.Modular.Positive.Packed.P065
public import Li2Unified.Modular.Positive.Packed.P066
public import Li2Unified.Modular.Positive.Packed.P067
public import Li2Unified.Modular.Positive.Packed.P042
public import Li2Unified.Modular.Positive.Packed.P051
public import Li2Unified.Modular.Positive.Packed.P002
public import Li2Unified.Modular.Base.PrimeReferenceDeterminant
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix
public import Li2Unified.Modular.Base.PrimitiveReduction
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Tactic

set_option backward.privateInPublic true

@[expose] public section

section
/-! Finite exceptional sets and arbitrary thresholds. Prime-only decay
is handled by an explicitly strictly increasing sequence of indices p_j-1. -/
open Polynomial Filter Topology
namespace Li2Unified.ParameterFamily
noncomputable section

def PrimeEdgeReduction (lam : ℚ) (bad : Finset ℕ) (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → N < p → p ∉ bad →
    ∃ c : ZMod p, c ≠ 0 ∧ (P lam (p-1)).map (Int.castRingHom (ZMod p)) = C c

lemma exists_allowed_prime (bad : Finset ℕ) (N M : ℕ) :
    ∃ p : ℕ, M ≤ p-1 ∧ p.Prime ∧ N < p ∧ p ∉ bad := by
  obtain ⟨p, hpbig, hp⟩ :=
    Nat.exists_infinite_primes (max (M+2) (max (N+1) (bad.sup id + 1)))
  have hbad : p ∉ bad := by
    intro hmem
    have hle : p ≤ bad.sup id := Finset.le_sup (f := id) hmem
    omega
  exact ⟨p, by omega, hp, by omega, hbad⟩

theorem frequently_rational_nonzero_of_finite_prime_reduction
    (polys : ℕ → ℤ[X]) (bad : Finset ℕ) (N : ℕ)
    (hred : ∀ p : ℕ, p.Prime → N < p → p ∉ bad →
      ∃ c : ZMod p, c ≠ 0 ∧ (polys (p-1)).map (Int.castRingHom (ZMod p)) = C c)
    (q : ℚ) : ∃ᶠ n in atTop, aeval (q : ℝ) (polys n) ≠ 0 := by
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨p, hpbig, hp, hN, hbad⟩ := exists_allowed_prime bad N (max M q.den)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc, hcp⟩ := hred p hp hN hbad
  refine ⟨p-1, by omega,
    Li2.rational_nonzero_of_constant_reduction (polys (p-1)) p c hc hcp q ?_⟩
  intro hz
  have hdvd : p ∣ q.den := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hden : q.den < p := by omega
  exact (not_le.mpr hden) (Nat.le_of_dvd q.den_pos hdvd)

lemma frequently_allowed_indices (bad : Finset ℕ) (N : ℕ) :
    ∃ᶠ n : ℕ in atTop, (n+1).Prime ∧ N < n+1 ∧ n+1 ∉ bad := by
  rw [Filter.frequently_atTop]
  intro M
  obtain ⟨p, hpbig, hp, hN, hbad⟩ := exists_allowed_prime bad N M
  refine ⟨p-1, hpbig, ?_⟩
  have hpos : 0 < p := hp.pos
  simpa only [Nat.sub_add_cancel hpos] using And.intro hp (And.intro hN hbad)

/-- Explicit index reparametrization; n_j+1 are allowed primes. -/
theorem exists_strictMono_prime_indices (bad : Finset ℕ) (N : ℕ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto ns atTop atTop ∧
      ∀ j, (ns j+1).Prime ∧ N < ns j+1 ∧ ns j+1 ∉ bad := by
  obtain ⟨u, hu, hallowed⟩ := exists_seq_forall_of_frequently (frequently_allowed_indices bad N)
  obtain ⟨v, hv, huv⟩ := strictMono_subseq_of_tendsto_atTop hu
  exact ⟨u ∘ v, huv, huv.tendsto_atTop, fun j => hallowed (v j)⟩

/-- The bound is required only at sufficiently large allowed prime indices.
The exponent/degree use n_j itself, never the enumeration index j. -/
theorem irrational_of_prime_subsequence_gaussian
    (ξ : ℝ) (polys : ℕ → ℤ[X]) (D : ℕ) (bad : Finset ℕ) (N : ℕ)
    (hdeg : ∀ n, (polys n).natDegree ≤ D*n) {c : ℝ} (hc : 0 < c)
    (hred : ∀ p : ℕ, p.Prime → N < p → p ∉ bad →
      ∃ a : ZMod p, a ≠ 0 ∧ (polys (p-1)).map (Int.castRingHom (ZMod p)) = C a)
    (hbound : ∀ᶠ n : ℕ in atTop, (n+1).Prime → N < n+1 → n+1 ∉ bad →
      |aeval ξ (polys n)| ≤ Real.exp (-c*(n:ℝ)^2)) :
    Irrational ξ := by
  obtain ⟨ns, hmono, ht, ha⟩ := exists_strictMono_prime_indices bad N
  apply Li2.irrational_of_int_polynomials ξ (fun j => polys (ns j)) (fun j => D*ns j)
  · exact fun j => hdeg (ns j)
  · intro b hb
    have hg := (Li2.tendsto_pow_mul_exp_neg_sq_of_pos hc D b hb).comp ht
    refine squeeze_zero' (Eventually.of_forall fun j =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg b) _) (abs_nonneg _)) ?_ hg
    filter_upwards [ht.eventually hbound] with j hj
    exact mul_le_mul_of_nonneg_left (hj (ha j).1 (ha j).2.1 (ha j).2.2)
      (pow_nonneg (Nat.cast_nonneg b) _)
  · intro q
    apply Filter.Eventually.frequently
    filter_upwards [ht.eventually (eventually_ge_atTop q.den)] with j hj
    letI : Fact (ns j+1).Prime := ⟨(ha j).1⟩
    obtain ⟨a, ha0, hared⟩ := hred (ns j+1) (ha j).1 (ha j).2.1 (ha j).2.2
    have heq : ns j+1-1 = ns j := by omega
    rw [heq] at hared
    apply Li2.rational_nonzero_of_constant_reduction (polys (ns j)) (ns j+1) a ha0 hared q
    intro hz
    have hdvd : ns j+1 ∣ q.den := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hle := Nat.le_of_dvd q.den_pos hdvd
    omega

theorem irrational_r_of_prime_decay (lam : ℚ) (bad : Finset ℕ) (N : ℕ)
    {c : ℝ} (hc : 0 < c) (hedge : PrimeEdgeReduction lam bad N)
    (hbound : ∀ᶠ n : ℕ in atTop, (n+1).Prime → N < n+1 → n+1 ∉ bad →
      |aeval (r lam) (P lam n)| ≤ Real.exp (-c*(n:ℝ)^2)) : Irrational (r lam) :=
  irrational_of_prime_subsequence_gaussian (r lam) (P lam) 2 bad N (P_natDegree_le lam)
    hc hedge hbound

theorem irrational_r_of_gaussian (lam : ℚ) (bad : Finset ℕ) (N : ℕ)
    {c : ℝ} (hc : 0 < c) (hedge : PrimeEdgeReduction lam bad N)
    (hbound : ∀ᶠ n : ℕ in atTop, |aeval (r lam) (P lam n)| ≤ Real.exp (-c*(n:ℝ)^2)) :
    Irrational (r lam) := by
  apply irrational_r_of_prime_decay lam bad N hc hedge
  filter_upwards [hbound] with n hn
  exact fun _ _ _ => hn

end
end Li2Unified.ParameterFamily

end

section
open Polynomial
open scoped BigOperators
namespace Li2Unified.Stage0.HalfPrimeEdge
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Proofs.PrimeEdge

/-- UNIFIED §4 parameter weight; the legacy weight contains (-2)^a. -/
def lowWeight (a : ℕ) : ℚ :=
  lambda⁻¹^a * (-(a:ℚ)) * Li2.primeLowRationalUnit a

def actualMatrix (p : ℕ) (hp4 : 3 < p) :
    Matrix (Li2.PrimeBlockIndex p) (Li2.PrimeBlockIndex p) ℚ[X] :=
  fun x y => C (Li2.primeBlockUnitScale hp4 x * Li2.primeBlockUnitScale hp4 y) *
    numeratorFunctional lambda (4*(p-1))
      ((Li2.D (p-1))^3 *
       (Li2.primeOriginalBasis p (by omega)
         ((Li2.primeOriginalBlockEquiv hp4).symm x)).map (Int.castRingHom ℚ) *
       (Li2.primeOriginalBasis p (by omega)
         ((Li2.primeOriginalBlockEquiv hp4).symm y)).map (Int.castRingHom ℚ))

theorem actualMatrix_det_original_Q (p : ℕ) (hp4 : 3 < p) :
    (actualMatrix p hp4).det = C (Li2.primeNormalizedDetScale hp4) * Instances.PosHalf.Q (p-1) := by
  classical
  let E : Fin (2*(p-1)) → ℚ[X] := fun a =>
    (Li2.primeOriginalBasis p (by omega) a).map (Int.castRingHom ℚ)
  let M : Matrix (Fin (2*(p-1))) (Fin (2*(p-1))) ℚ[X] :=
    Matrix.of fun a b => numeratorFunctional lambda (4*(p-1))
      ((Li2.D (p-1))^3 * E a * E b)
  let B : Matrix (Li2.PrimeBlockIndex p) (Li2.PrimeBlockIndex p) ℚ[X] :=
    M.submatrix (Li2.primeOriginalBlockEquiv hp4).symm
      (Li2.primeOriginalBlockEquiv hp4).symm
  have he : actualMatrix p hp4 =
      Matrix.of (fun x y => C (Li2.primeBlockUnitScale hp4 x) *
        (C (Li2.primeBlockUnitScale hp4 y) * B x y)) := by
    ext x y
    simp only [actualMatrix, Matrix.of_apply, B, M, E, Matrix.submatrix_apply, C_mul]
    ring
  rw [he, Matrix.det_mul_column]
  change (∏ x : Li2.PrimeBlockIndex p, C (Li2.primeBlockUnitScale hp4 x)) *
    (Matrix.of (fun x y => C (Li2.primeBlockUnitScale hp4 y) * B x y)).det = _
  rw [Matrix.det_mul_row]
  have hb : B.det = M.det :=
    Matrix.det_submatrix_equiv_self (Li2.primeOriginalBlockEquiv hp4).symm _
  have hE : ∀ a, (E a).natDegree < 2*(p-1) := fun a =>
    Polynomial.natDegree_map_le.trans_lt (Li2.primeOriginalBasis_natDegree_lt p (by omega) a)
  have hm : M.det = C ((Li2.coeffMat E).det^2) * ParameterFamily.Q lambda (p-1) :=
    original_gram_basis_change lambda (p-1) E hE
  rw [hb, hm, ← map_prod]
  simp only [Li2.primeNormalizedDetScale, Instances.PosHalf.Q, E, mul_pow, C_mul, C_pow]
  ring

/-- The corner is constrained by actual entrywise comparison, not defined
backwards from its desired determinant. Both identification tasks stay open. -/
theorem actual_matrix_block_comparison
    (p : ℕ) [Fact p.Prime] (hp4 : 3 < p) (hbad : p ∉ badPrimes) :
    ∃ corner : Matrix (Fin 6) (Fin 6) ℚ,
      corner.det = cornerBlockConstant lambda ∧
      ∀ x y : Li2.PrimeBlockIndex p,
        Li2.GV p
          (actualMatrix p hp4 x y - C ((p:ℚ)^
            (Li2.primeReferenceRowExponent x + Li2.primeReferenceColExponent y) *
            (match x, y with
             | Sum.inl ai, Sum.inl bi =>
                 if ai.1 = bi.1 then
                   lowWeight (ai.1.val+1) * fixedLowBlock lambda ai.2 bi.2
                 else 0
             | Sum.inr i, Sum.inr j => corner i j
             | _, _ => 0)))
          (Li2.primeBlockWeight x + Li2.primeBlockWeight y + 1/2) := by
  let corner := Li2Unified.Proofs.PrimeEdge.fixedCornerBlock lambda
  refine ⟨corner, Li2Unified.Proofs.PrimeEdge.fixedCornerBlock_det lambda
    lambda_nonzero lambda_ne_one, ?_⟩
  intro x y
  have hM : actualMatrix p hp4 x y =
      Li2Unified.Proofs.PrimeEdge.parameterNormalizedMatrix lambda hp4 x y := by
    simp only [actualMatrix, Li2Unified.Proofs.PrimeEdge.parameterNormalizedMatrix,
      Li2Unified.Proofs.PrimeEdge.parameterOriginalNumeratorEntry, Polynomial.map_mul,
      mul_assoc]
  have h := Li2Unified.Proofs.PrimeEdge.parameterEntryReference_entry_GV lambda
    lambda_abs_lt_one (parameter_units p hbad).1 (parameter_units p hbad).2.1
    (parameter_fermat p hbad) hp4 x y
  rw [Li2Unified.Proofs.PrimeEdge.parameterEntryReference_literal] at h
  simpa only [hM, lowWeight, Li2Unified.Proofs.PrimeEdge.parameterLowRationalWeight]
    using h

theorem scaled_original_Q_congruence
    (p : ℕ) [Fact p.Prime] (hp4 : 3 < p) (hbad : p ∉ badPrimes) :
    ∃ s c : ℚ, s ≠ 0 ∧ c ≠ 0 ∧ padicValRat p c = 0 ∧
      Li2.GV p (C s * Instances.PosHalf.Q (p-1) - C c) 1 := by
  classical
  let corner := fixedCornerBlock lambda
  let M := parameterNormalizedMatrix lambda hp4
  have hM : actualMatrix p hp4 = M := by
    funext x y
    simp only [actualMatrix, M, parameterNormalizedMatrix,
      parameterOriginalNumeratorEntry, Polynomial.map_mul, mul_assoc]
  have hN : ∀ x y, Li2.GV p (parameterReferenceMatrix lambda p corner x y)
      (Li2.primeBlockWeight x + Li2.primeBlockWeight y) :=
    parameterReferenceMatrix_GV_of_block_bounds lambda corner hp4
      (parameter_units p hbad).1
      (by simpa only [lambda] using fixedLowBlock_half_VG p hp4)
      (by simpa only [corner, lambda] using fixedCornerBlock_half_VG p hp4)
  have herr : ∀ x y, Li2.GV p (M x y - parameterReferenceMatrix lambda p corner x y)
      (Li2.primeBlockWeight x + Li2.primeBlockWeight y + 1/2) :=
    parameterNormalizedMatrix_reference_GV lambda lambda_abs_lt_one
      (parameter_units p hbad).1 (parameter_units p hbad).2.1
      (parameter_fermat p hbad) hp4
  have hd := parameterMatrix_scaled_det_GV lambda corner M hp4 hN herr
  have hc := posHalf_referenceCore_unit corner hp4 hbad
    (fixedCornerBlock_det lambda lambda_nonzero lambda_ne_one)
  refine ⟨Li2.primeQEdgeScale hp4, (parameterReferenceCore lambda p corner).det,
    (Li2.primeQEdgeScale_spec hp4).1, hc.1, hc.2, ?_⟩
  rw [← hM, actualMatrix_det_original_Q] at hd
  simpa only [Li2.primeQEdgeScale, C_mul, mul_assoc] using hd

theorem edge_reduction : PrimeEdgeReduction lambda badPrimes 5 := by
  intro p hp hp5 hbad
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, c, hs, hc, hcv, hcong⟩ :=
    scaled_original_Q_congruence p (by omega) hbad
  have hQ : Instances.PosHalf.Q (p-1) ≠ 0 := by
    intro hz
    have hzero : Li2.VG p (-c) 1 := by
      simpa [hz] using hcong 0
    rcases hzero with hz | hv
    · exact hc (neg_eq_zero.mp hz)
    · rw [padicValRat.neg, hcv] at hv
      norm_num at hv
  exact Li2.primitive_constant_reduction_of_scaled_congruence
    (Instances.PosHalf.P (p-1)) (Instances.PosHalf.P_isPrimitive (p-1) hQ)
    (Instances.PosHalf.Q (p-1)) (d lambda (p-1)) s c
    (d_pos lambda (p-1)).ne' hs (P_eq_d_Q lambda (p-1)) hc hcv hcong

end
end Li2Unified.Stage0.HalfPrimeEdge

end

section
/-! One-variable log integrability on a finite affine line cell.
Constant/degenerate curves are permitted here because Real.log is total;
this lemma alone does not provide almost-everywhere noncollision. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "LineLog: imports loaded"
  out.flush

lemma intervalIntegrable_log_line (c v w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖c+(t:ℂ)*v-w‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t _
  apply AnalyticAt.meromorphicAt
  have hc : AnalyticAt ℝ (fun _ : ℝ => c) t := analyticAt_const
  have hv : AnalyticAt ℝ (fun _ : ℝ => v) t := analyticAt_const
  have hw : AnalyticAt ℝ (fun _ : ℝ => w) t := analyticAt_const
  exact (hc.add ((Complex.ofRealCLM.analyticAt t).mul hv)).sub hw


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "LineLog: interval integrability complete"
  out.flush

lemma integrable_log_line_measure (c v w : ℂ) (a b density : ℝ) :
    Integrable (fun z : ℂ => Real.log ‖z-w‖)
      (ENNReal.ofReal density • Measure.map (fun t : ℝ => c+(t:ℂ)*v)
        (volume.restrict (Ioc a b))) := by
  have hg : Measurable (fun z : ℂ => Real.log ‖z-w‖) := by fun_prop
  have hf : Measurable (fun t : ℝ => c+(t:ℂ)*v) := by fun_prop
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).2
  exact (intervalIntegrable_log_line c v w a b).1


#eval show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "LineLog: measure integrability complete"
  out.flush

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! A finite rational input compiler for positive-star measures.
Each input is a uniform horizontal [0,r] or vertical [-r,r] layer. The
measure is defined directly, before its mass or logarithmic integrals. -/
open MeasureTheory Set
namespace Li2Unified.ParameterFamily.Energy
noncomputable section

structure StarLayer where
  radius : ℚ
  density : ℚ
  vertical : Bool

namespace StarLayer

def Valid (s : StarLayer) : Prop := 0 ≤ s.radius ∧ 0 ≤ s.density
def left (s : StarLayer) : ℝ := if s.vertical then -(s.radius : ℝ) else 0
def right (s : StarLayer) : ℝ := s.radius
def direction (s : StarLayer) : ℂ := if s.vertical then Complex.I else 1
def mass (s : StarLayer) : ℚ :=
  if s.vertical then 2*s.density*s.radius else s.density*s.radius
def measure (s : StarLayer) : Measure ℂ :=
  ENNReal.ofReal (s.density : ℝ) • Measure.map (fun x : ℝ => (x:ℂ)*s.direction)
    (volume.restrict (Ioc s.left s.right))

lemma mass_nonneg (s : StarLayer) (hs : s.Valid) : 0 ≤ s.mass := by
  obtain ⟨hr, hd⟩ := hs
  unfold mass
  split <;> positivity

lemma measure_univ (s : StarLayer) (hs : s.Valid) :
    s.measure univ = ENNReal.ofReal (s.mass : ℝ) := by
  have hf : Measurable (fun x : ℝ => (x:ℂ)*s.direction) := by fun_prop
  have hd : (0:ℝ) ≤ s.density := by exact_mod_cast hs.2
  have he : (s.density : ℝ)*(s.right-s.left) = (s.mass : ℝ) := by
    cases hv : s.vertical <;> simp [right, left, mass, hv] <;> ring
  simp only [measure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hf MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Ioc]
  rw [← ENNReal.ofReal_mul hd, he]

lemma integrable_log (s : StarLayer) (w : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z-w‖) s.measure := by
  simpa only [measure, zero_add] using
    integrable_log_line_measure 0 s.direction w s.left s.right (s.density : ℝ)

end StarLayer

def starLayerMass : List StarLayer → ℚ
  | [] => 0
  | s :: ss => s.mass + starLayerMass ss

def starLayerMeasure : List StarLayer → Measure ℂ
  | [] => 0
  | s :: ss => s.measure + starLayerMeasure ss

lemma starLayerMass_nonneg (ss : List StarLayer) (hs : ∀ s ∈ ss, s.Valid) :
    0 ≤ starLayerMass ss := by
  induction ss with
  | nil => simp [starLayerMass]
  | cons s ss ih =>
    exact add_nonneg (s.mass_nonneg (hs s (by simp)))
      (ih (fun t ht => hs t (by simp [ht])))

theorem starLayerMeasure_univ (ss : List StarLayer) (hs : ∀ s ∈ ss, s.Valid) :
    starLayerMeasure ss univ = ENNReal.ofReal (starLayerMass ss : ℝ) := by
  induction ss with
  | nil => simp [starLayerMeasure, starLayerMass]
  | cons s ss ih =>
    have ht : ∀ t ∈ ss, t.Valid := fun t ht => hs t (by simp [ht])
    have hc : s.Valid := hs s (by simp)
    have hm : (0:ℝ) ≤ s.mass := by exact_mod_cast s.mass_nonneg hc
    have hms : (0:ℝ) ≤ starLayerMass ss := by exact_mod_cast starLayerMass_nonneg ss ht
    simp only [starLayerMeasure, Measure.add_apply, s.measure_univ hc, ih ht,
      starLayerMass, Rat.cast_add, ENNReal.ofReal_add hm hms]

theorem starLayerMeasure_probability (ss : List StarLayer)
    (hs : ∀ s ∈ ss, s.Valid) (hm : starLayerMass ss = 1) :
    IsProbabilityMeasure (starLayerMeasure ss) := by
  constructor
  rw [starLayerMeasure_univ ss hs, hm]
  norm_num

theorem integrable_log_starLayerMeasure (ss : List StarLayer) (w : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z-w‖) (starLayerMeasure ss) := by
  induction ss with
  | nil => simp [starLayerMeasure]
  | cons s ss ih => exact (s.integrable_log w).add_measure ih

end
end Li2Unified.ParameterFamily.Energy

end

section
/-! Independent 36-layer comparison measure for lambda=1/2.
Derived by retaining the first20 original ray cells and averaging subsequent
blocks of10, then collecting positive nested layers. Original cert-q2.json is
unchanged. Only input/mass/one-variable L1 is proved here, not energy or S. -/
open MeasureTheory
namespace Li2Unified.Instances.PosHalf.LayerComparison
noncomputable section
open Li2Unified.ParameterFamily.Energy

def layerData : List StarLayer := [
  ⟨7/100, 5486000/100000027, false⟩,
  ⟨7/50, 3870700/100000027, false⟩,
  ⟨21/100, 2913000/100000027, false⟩,
  ⟨7/25, 2327000/100000027, false⟩,
  ⟨7/20, 1932800/100000027, false⟩,
  ⟨21/50, 1648500/100000027, false⟩,
  ⟨49/100, 1433000/100000027, false⟩,
  ⟨14/25, 1263800/100000027, false⟩,
  ⟨63/100, 1127200/100000027, false⟩,
  ⟨7/10, 1014700/100000027, false⟩,
  ⟨77/100, 920500/100000027, false⟩,
  ⟨21/25, 840300/100000027, false⟩,
  ⟨91/100, 771500/100000027, false⟩,
  ⟨49/50, 711800/100000027, false⟩,
  ⟨21/20, 659400/100000027, false⟩,
  ⟨28/25, 613300/100000027, false⟩,
  ⟨119/100, 572300/100000027, false⟩,
  ⟨63/50, 535800/100000027, false⟩,
  ⟨133/100, 503000/100000027, false⟩,
  ⟨7/5, 2230420/100000027, false⟩,
  ⟨21/10, 2947820/100000027, false⟩,
  ⟨14/5, 2013740/100000027, false⟩,
  ⟨7/2, 1498080/100000027, false⟩,
  ⟨21/5, 1181890/100000027, false⟩,
  ⟨49/10, 974840/100000027, false⟩,
  ⟨28/5, 833640/100000027, false⟩,
  ⟨63/10, 735770/100000027, false⟩,
  ⟨7, 668860/100000027, false⟩,
  ⟨77/10, 626710/100000027, false⟩,
  ⟨42/5, 607930/100000027, false⟩,
  ⟨91/10, 617440/100000027, false⟩,
  ⟨49/5, 677410/100000027, false⟩,
  ⟨21/2, 958380/100000027, false⟩,
  ⟨56/5, 929970/100000027, false⟩,
  ⟨1/25, 3687200/100000027, true⟩,
  ⟨2/25, 3178600/100000027, true⟩
]

lemma layerData_length : layerData.length = 36 := by norm_num [layerData]
lemma layerData_valid : ∀ s ∈ layerData, s.Valid := by
  norm_num [layerData, StarLayer.Valid]
lemma layerData_radii : ∀ s ∈ layerData, 0 < s.radius ∧ s.radius ≤ 56/5 := by
  norm_num [layerData]
lemma layerData_mass : starLayerMass layerData = 1 := by
  norm_num [starLayerMass, layerData, StarLayer.mass]
lemma layerData_density_bound :
    2 * (layerData.map StarLayer.density).sum ≤ (11/10:ℚ) := by
  norm_num [layerData]

def comparisonMeasure : Measure ℂ := starLayerMeasure layerData
instance comparison_probability : IsProbabilityMeasure comparisonMeasure :=
  starLayerMeasure_probability layerData layerData_valid layerData_mass

lemma integrable_log_comparisonMeasure (w : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z-w‖) comparisonMeasure :=
  integrable_log_starLayerMeasure layerData w

def comparisonPotential (w : ℂ) : ℝ :=
  ∫ z : ℂ, Real.log ‖z-w‖ ∂comparisonMeasure

def comparisonEnergy : ℝ :=
  ∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(comparisonMeasure.prod comparisonMeasure)

end
end Li2Unified.Instances.PosHalf.LayerComparison

end


end
