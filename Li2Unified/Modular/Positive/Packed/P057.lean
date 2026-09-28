module
public import Li2Unified.Modular.Positive.Packed.P056
public import Li2Unified.Modular.Base.PrimeCrossDiscBounds
public import Li2Unified.Modular.Base.PrimeRemainingCrossBounds
public import Li2Unified.Modular.Base.PrimeCrossValuation
public import Li2Unified.Modular.Base.PrimeNormalizedMatrix
public import Li2Unified.Modular.Positive.Packed.P054

set_option backward.privateInPublic true

@[expose] public section

section
open Polynomial Li2 Li2Unified.LambdaLift
open scoped BigOperators
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDiscContribution_cube_factor_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p)
    (T : ℤ[X]) (a : Fin p) (m : ℕ)
    (hT : ∃ E : ℤ[X], T.comp (primeDiscSubstitution p a) = C ((p:ℤ)^m)*E)
    (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(m+primeDiscCubeGain a) := by
  by_cases hz : a.val = 0
  · have he : a = (⟨0,by omega⟩ : Fin p) := Fin.ext hz
    rw [he] at hT ⊢
    rw [parameterDiscContribution_cube_zero]
    simpa only [primeDiscCubeGain, Fin.val_mk, ite_true, Nat.add_zero, coeff_map, norm_pow] using!
      parameterDiscTest_U_substituted_factor_bound (lam^p) (parameter_power_unit lam hu) hreg hp4 T (⟨0,by omega⟩ : Fin p) m
        (parameterIntegralEta lam hu hreg) hT n
  · by_cases hl : a.val ≤ p-4
    · have h : ∀ l, ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 a T
          (parameterIntegralEta lam hu hreg)).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff l‖ ≤ ‖(p:ℚ_[p])‖^m := by
        intro l
        simpa only [coeff_map,norm_pow] using! parameterDiscTestScaled_factor_bound (lam^p) (parameter_power_unit lam hu) hreg hp4 T a m
          (parameterIntegralEta lam hu hreg) hT l
      have he : C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T =
          C ((p:ℚ_[p])^1)*(C ((p:ℚ_[p])^2)*parameterDiscContribution lam hu hreg hp4 a T) := by
        simp only [C_pow]
        ring
      rw [he,parameterDiscContribution_scaled_low lam hu hreg hp4 a (by omega) hl,
        primeDiscCubeGain,if_neg hz,if_pos hl]
      simpa only [Nat.add_comm] using! fieldPolynomial_prime_power_bound _ 1 m h n
    · have h : ∀ l, ‖((parameterDiscTestScaled (lam^p) (parameter_power_unit lam hu) hreg hp4 a T
          (parameterIntegralEta lam hu hreg)).map
          (algebraMap ℤ_[p] ℚ_[p])).coeff l‖ ≤ ‖(p:ℚ_[p])‖^m := by
        intro l
        simpa only [coeff_map,norm_pow] using! parameterDiscTestScaled_factor_bound (lam^p) (parameter_power_unit lam hu) hreg hp4 T a m
          (parameterIntegralEta lam hu hreg) hT l
      have he : C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T =
          C ((p:ℚ_[p])^2)*(C (p:ℚ_[p])*parameterDiscContribution lam hu hreg hp4 a T) := by
        simp only [C_pow]
        ring
      rw [he,parameterDiscContribution_linear_high lam hu hreg hp4 a (by omega),
        primeDiscCubeGain,if_neg hz,if_neg hl]
      simpa only [Nat.add_comm] using! fieldPolynomial_prime_power_bound _ 2 m h n


theorem parameterOriginalBasisProduct_cube_disc_bound (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0) (hp4 : 3 < p)
    (i j : Fin (2*(p-1))) (a : Fin p) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a
      (primeOriginalBasis p (by omega) i*primeOriginalBasis p (by omega) j)).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(primeOriginalBasisLocalOrder p (by omega) i a+
        primeOriginalBasisLocalOrder p (by omega) j a+primeDiscCubeGain a) := by
  obtain ⟨A,hA⟩ := primeOriginalBasisProduct_disc_factor p (by omega) i j a
  apply parameterDiscContribution_cube_factor_bound lam hu hreg hp4
  exact ⟨X^(primeOriginalBasisLocalOrder p (by omega) i a+
    primeOriginalBasisLocalOrder p (by omega) j a)*A,by rw [hA,mul_assoc]⟩


theorem parameterNumerator_cube_bound_of_disc_bounds (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (T : ℤ[X]) (k : ℕ)
    (hdisc : ∀ a : Fin p, ∀ n,
      ‖(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k)
    (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k := by
  have he : C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*T.map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p]) =
      ∑ a : Fin p, C ((lam:ℚ_[p])⁻¹^a.val)*(C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T) := by
    rw [parameterNumerator_global_dissection lam hlam hu hreg hp4 hz1,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he,finset_sum_coeff]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro a _
  have h := fieldPolynomial_integral_weight_bound
    (C ((p:ℚ_[p])^3)*parameterDiscContribution lam hu hreg hp4 a T)
    (integralParameterInvPow lam hu.1 hu.2 a.val) _ (hdisc a) n
  simpa only [integralParameterInvPow,integralRational,Rat.cast_pow,Rat.cast_inv,PadicInt.coe_pow,PadicInt.coe_neg,PadicInt.coe_natCast] using! h


theorem parameterLow_cross_original_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b)) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeJetPoly p ⟨a,i⟩*primeJetPoly p ⟨b,j⟩).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+j.val+2) := by
  apply parameterNumerator_cube_bound_of_disc_bounds lam hlam hu hreg hz1 hp4 _ (i.val+j.val+2)
  intro c l
  have h := parameterDiscContribution_cube_factor_bound lam hu hreg hp4 _ c
    (primeJetLocalOrder p ⟨a,i⟩ c+primeJetLocalOrder p ⟨b,j⟩ c)
    (primeJet_pair_disc_factor ⟨a,i⟩ ⟨b,j⟩ c) l
  exact h.trans (pow_le_pow_of_le_one (norm_nonneg _)
    (PadicInt.norm_le_one (p:ℤ_[p]))
    (primeLow_cross_cube_order hp4 a b ha0 ha hb0 hb hab i j c))


theorem parameterTop_low_original_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p) (a : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a)) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeProduct p*primeJetPoly p ⟨a,i⟩).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+3) := by
  apply parameterNumerator_cube_bound_of_disc_bounds lam hlam hu hreg hz1 hp4 _ (i.val+3)
  intro c l
  have h := parameterDiscContribution_cube_factor_bound lam hu hreg hp4 _ c
    (primeMultiplicity p c+primeJetLocalOrder p ⟨a,i⟩ c)
    (primeProduct_jet_disc_factor ⟨a,i⟩ c) l
  exact h.trans (pow_le_pow_of_le_one (norm_nonneg _)
    (PadicInt.norm_le_one (p:ℤ_[p]))
    (primeTop_low_cube_order hp4 a ha0 ha i c))


theorem parameterOriginalBasis_low_cross_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+j.val+2) := by
  rw [primeOriginalBasis_eq_jet_of_index (by omega) I ⟨a,i⟩ hI,
    primeOriginalBasis_eq_jet_of_index (by omega) J ⟨b,j⟩ hJ]
  exact parameterLow_cross_original_entry_bound lam hlam hu hreg hz1 hp4 a b ha0 ha hb0 hb hab i j n


theorem parameterOriginalBasis_top_low_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (J : Fin (2*(p-1))) (a : Fin p) (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a))
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) (⟨0,by omega⟩ : Fin (2*(p-1)))*
          primeOriginalBasis p (by omega) J).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^(i.val+3) := by
  rw [primeOriginalBasis_zero_eq_product (by omega),
    primeOriginalBasis_eq_jet_of_index (by omega) J ⟨a,i⟩ hJ]
  exact parameterTop_low_original_entry_bound lam hlam hu hreg hz1 hp4 a ha0 ha i n

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterOriginalBasis_low_cross_entry_bound
#print axioms Li2Unified.Proofs.PrimeEdge.parameterOriginalBasis_top_low_entry_bound

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem parameterDistinctJet_original_cube_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p) (a b : PrimeJet p)
    (hab : a.1 ≠ b.1) (k : ℕ)
    (ha : k ≤ a.2.val+primeMultiplicity p a.1+primeDiscCubeGain a.1)
    (hb : k ≤ b.2.val+primeMultiplicity p b.1+primeDiscCubeGain b.1)
    (hk : k ≤ 4) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeJetPoly p a*primeJetPoly p b).map (Int.castRingHom ℚ))).map
        (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k := by
  apply parameterNumerator_cube_bound_of_disc_bounds lam hlam hu hreg hz1 hp4 _ k
  intro c l
  have h := parameterDiscContribution_cube_factor_bound lam hu hreg hp4 _ c _
    (primeJet_pair_disc_factor a b c) l
  exact h.trans (pow_le_pow_of_le_one (norm_nonneg _)
    (PadicInt.norm_le_one (p:ℤ_[p])) (primeDistinctJet_cube_order hp4 a b hab k ha hb hk c))

theorem parameterOriginalBasis_distinct_jet_cube_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : PrimeJet p)
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm a).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm b).succ)
    (hab : a.1 ≠ b.1) (k : ℕ)
    (ha : k ≤ a.2.val+primeMultiplicity p a.1+primeDiscCubeGain a.1)
    (hb : k ≤ b.2.val+primeMultiplicity p b.1+primeDiscCubeGain b.1)
    (hk : k ≤ 4) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤ ‖(p:ℚ_[p])‖^k := by
  rw [primeOriginalBasis_eq_jet_of_index (by omega) I a hI,
    primeOriginalBasis_eq_jet_of_index (by omega) J b hJ]
  exact parameterDistinctJet_original_cube_bound lam hlam hu hreg hz1 hp4 a b hab k ha hb hk n

/-- Low_i versus zero_j: cube order j+2; strict raw margin 3/2-i. -/
theorem parameterOriginalBasis_low_zero_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb0 : b.val = 0)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(j.val+2) := by
  have hmA := primeMultiplicity_low hp4 a ha
  have hmB : primeMultiplicity p b = 2 := primeMultiplicity_low hp4 b (by omega)
  have hj : j.val ≤ 1 := by
    have h := j.isLt
    omega
  have hab : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    omega
  refine parameterOriginalBasis_distinct_jet_cube_bound lam hlam hu hreg hz1 hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab (j.val+2) ?_ ?_ ?_ n
  · simp only [hmA,primeDiscCubeGain,if_neg ha0.ne',if_pos ha] <;> omega
  · simp only [hmB,primeDiscCubeGain,if_pos hb0] <;> omega
  · omega

/-- Low_i versus high: cube order 3; strict raw margin 3/2-i. -/
theorem parameterOriginalBasis_low_high_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^3 := by
  have hmA := primeMultiplicity_low hp4 a ha
  have hmB : primeMultiplicity p b = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hj : j.val = 0 := by
    have h := j.isLt
    omega
  have hab : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    omega
  refine parameterOriginalBasis_distinct_jet_cube_bound lam hlam hu hreg hz1 hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab 3 ?_ ?_ ?_ n
  · simp only [hmA,primeDiscCubeGain,if_neg ha0.ne',if_pos ha] <;> omega
  · simp only [hj,hmB,primeDiscCubeGain,if_neg (by omega : b.val ≠ 0),
      if_neg (by omega : ¬ b.val ≤ p-4)] <;> omega
  · omega

/-- Zero_i versus high: one full order above the row-weight sum. -/
theorem parameterOriginalBasis_zero_high_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : a.val = 0) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^(i.val+2) := by
  have hmA : primeMultiplicity p a = 2 := primeMultiplicity_low hp4 a (by omega)
  have hmB : primeMultiplicity p b = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hi : i.val ≤ 1 := by
    have h := i.isLt
    omega
  have hj : j.val = 0 := by
    have h := j.isLt
    omega
  have hab : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    omega
  refine parameterOriginalBasis_distinct_jet_cube_bound lam hlam hu hreg hz1 hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab (i.val+2) ?_ ?_ ?_ n
  · simp only [hmA,primeDiscCubeGain,if_pos ha0] <;> omega
  · simp only [hj,hmB,primeDiscCubeGain,if_neg (by omega : b.val ≠ 0),
      if_neg (by omega : ¬ b.val ≤ p-4)] <;> omega
  · omega

/-- Two distinct high jets: one full order above the weight sum. -/
theorem parameterOriginalBasis_high_cross_entry_bound (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha : p-4 < a.val) (hb : p-4 < b.val) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) (n : ℕ) :
    ‖(C ((p:ℚ_[p])^3)*
      (Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3*
        (primeOriginalBasis p (by omega) I*primeOriginalBasis p (by omega) J).map
          (Int.castRingHom ℚ))).map (Rat.castHom ℚ_[p])).coeff n‖ ≤
      ‖(p:ℚ_[p])‖^3 := by
  have hmA : primeMultiplicity p a = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hmB : primeMultiplicity p b = 1 := by
    unfold primeMultiplicity
    rw [if_neg (by omega)]
  have hi : i.val = 0 := by
    have h := i.isLt
    omega
  have hj : j.val = 0 := by
    have h := j.isLt
    omega
  refine parameterOriginalBasis_distinct_jet_cube_bound lam hlam hu hreg hz1 hp4 I J ⟨a,i⟩ ⟨b,j⟩
    hI hJ hab 3 ?_ ?_ ?_ n
  · simp only [hi,hmA,primeDiscCubeGain,if_neg (by omega : a.val ≠ 0),
      if_neg (by omega : ¬ a.val ≤ p-4)] <;> omega
  · simp only [hj,hmB,primeDiscCubeGain,if_neg (by omega : b.val ≠ 0),
      if_neg (by omega : ¬ b.val ≤ p-4)] <;> omega
  · omega

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterOriginalBasis_high_cross_entry_bound

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def parameterOriginalNumeratorEntry (lam : ℚ) (p : ℕ) (hp3 : 3 ≤ p)
    (I J : Fin (2*(p-1))) : ℚ[X] :=
  Li2Unified.ParameterFamily.numeratorFunctional lam (4*(p-1)) ((D (p-1))^3 *
    (primeOriginalBasis p hp3 I * primeOriginalBasis p hp3 J).map
      (Int.castRingHom ℚ))

lemma parameterOriginalNumeratorEntry_symm (lam : ℚ) (hp3 : 3 ≤ p)
    (I J : Fin (2*(p-1))) :
    parameterOriginalNumeratorEntry lam p hp3 I J = parameterOriginalNumeratorEntry lam p hp3 J I := by
  unfold parameterOriginalNumeratorEntry
  rw [mul_comm (primeOriginalBasis p hp3 I) (primeOriginalBasis p hp3 J)]

theorem parameterOriginalBasis_low_cross_GV_strict (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (hb0 : 0 < b.val) (hb : b.val ≤ p-4) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (parameterOriginalNumeratorEntry lam p (by omega) I J) ((((i.val : ℚ)-1)+((j.val : ℚ)-1))+(1)) ∧
    ∀ n, (parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-1)+((j.val : ℚ)-1)) < (padicValRat p ((parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound (parameterOriginalNumeratorEntry lam p (by omega) I J) (i.val+j.val+2)
    (parameterOriginalBasis_low_cross_entry_bound lam hlam hu hreg hz1 hp4 I J a b ha0 ha hb0 hb hab i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Low against zero; margin at least1/2. -/
theorem parameterOriginalBasis_low_zero_GV_strict (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb0 : b.val = 0)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (parameterOriginalNumeratorEntry lam p (by omega) I J) ((((i.val : ℚ)-1)+((j.val : ℚ)-3/2))+(3/2-(i.val : ℚ))) ∧
    ∀ n, (parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-1)+((j.val : ℚ)-3/2)) < (padicValRat p ((parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n) : ℚ) := by
  have hm := primeLow_index_margin hp4 a ha i
  refine GV.with_strict_margin ?_ (by linarith : (0 : ℚ) < 3/2-(i.val : ℚ))
  have h := GV_of_cube_padic_norm_bound (parameterOriginalNumeratorEntry lam p (by omega) I J) (j.val+2)
    (parameterOriginalBasis_low_zero_entry_bound lam hlam hu hreg hz1 hp4 I J a b ha0 ha hb0 i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Low against high; margin at least1/2. -/
theorem parameterOriginalBasis_low_high_GV_strict (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : 0 < a.val) (ha : a.val ≤ p-4) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (parameterOriginalNumeratorEntry lam p (by omega) I J) ((((i.val : ℚ)-1)+(-1/2 : ℚ))+(3/2-(i.val : ℚ))) ∧
    ∀ n, (parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-1)+(-1/2 : ℚ)) < (padicValRat p ((parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n) : ℚ) := by
  have hm := primeLow_index_margin hp4 a ha i
  refine GV.with_strict_margin ?_ (by linarith : (0 : ℚ) < 3/2-(i.val : ℚ))
  have h := GV_of_cube_padic_norm_bound (parameterOriginalNumeratorEntry lam p (by omega) I J) (3)
    (parameterOriginalBasis_low_high_entry_bound lam hlam hu hreg hz1 hp4 I J a b ha0 ha hb i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Zero against high inside the six-dimensional block; margin1. -/
theorem parameterOriginalBasis_zero_high_GV_strict (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha0 : a.val = 0) (hb : p-4 < b.val)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (parameterOriginalNumeratorEntry lam p (by omega) I J) ((((i.val : ℚ)-3/2)+(-1/2 : ℚ))+(1)) ∧
    ∀ n, (parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n = 0 ∨
      (((i.val : ℚ)-3/2)+(-1/2 : ℚ)) < (padicValRat p ((parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound (parameterOriginalNumeratorEntry lam p (by omega) I J) (i.val+2)
    (parameterOriginalBasis_zero_high_entry_bound lam hlam hu hreg hz1 hp4 I J a b ha0 hb i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Distinct high jets inside the six-dimensional block; margin1. -/
theorem parameterOriginalBasis_high_cross_GV_strict (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (I J : Fin (2*(p-1))) (a b : Fin p)
    (ha : p-4 < a.val) (hb : p-4 < b.val) (hab : a ≠ b)
    (i : Fin (primeMultiplicity p a)) (j : Fin (primeMultiplicity p b))
    (hI : finCongr (primeBasisSize p (by omega)) I =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ)
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨b,j⟩).succ) :
    GV p (parameterOriginalNumeratorEntry lam p (by omega) I J) (((-1/2 : ℚ)+(-1/2 : ℚ))+(1)) ∧
    ∀ n, (parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n = 0 ∨
      ((-1/2 : ℚ)+(-1/2 : ℚ)) < (padicValRat p ((parameterOriginalNumeratorEntry lam p (by omega) I J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound (parameterOriginalNumeratorEntry lam p (by omega) I J) (3)
    (parameterOriginalBasis_high_cross_entry_bound lam hlam hu hreg hz1 hp4 I J a b ha hb hab i j hI hJ)
  exact h.mono (by push_cast <;> linarith)

/-- Top G against a low block, with weights1/2 and i-1; margin1/2. -/
theorem parameterOriginalBasis_top_low_GV_strict (lam : ℚ) (hlam : |(lam:ℝ)| < 1)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hreg : VG p (lam^p/(1-lam^p)) 0)
    (hz1 : lam^p ≠ 1) (hp4 : 3 < p)
    (J : Fin (2*(p-1))) (a : Fin p) (ha0 : 0 < a.val) (ha : a.val ≤ p-4)
    (i : Fin (primeMultiplicity p a))
    (hJ : finCongr (primeBasisSize p (by omega)) J =
      ((primeJetEquiv p (by omega)).symm ⟨a,i⟩).succ) :
    GV p (parameterOriginalNumeratorEntry lam p (by omega)
      (⟨0,by omega⟩ : Fin (2*(p-1))) J)
      ((1/2 : ℚ)+((i.val : ℚ)-1)+1/2) ∧
    ∀ n, (parameterOriginalNumeratorEntry lam p (by omega)
      (⟨0,by omega⟩ : Fin (2*(p-1))) J).coeff n = 0 ∨
      (1/2 : ℚ)+((i.val : ℚ)-1) <
        (padicValRat p ((parameterOriginalNumeratorEntry lam p (by omega)
          (⟨0,by omega⟩ : Fin (2*(p-1))) J).coeff n) : ℚ) := by
  refine GV.with_strict_margin ?_ (by norm_num)
  have h := GV_of_cube_padic_norm_bound
    (parameterOriginalNumeratorEntry lam p (by omega)
      (⟨0,by omega⟩ : Fin (2*(p-1))) J) (i.val+3)
    (parameterOriginalBasis_top_low_entry_bound lam hlam hu hreg hz1 hp4 J a ha0 ha i hJ)
  exact h.mono (by push_cast <;> linarith)

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterOriginalBasis_high_cross_GV_strict
#print axioms Li2Unified.Proofs.PrimeEdge.parameterOriginalBasis_top_low_GV_strict

end

section
open Polynomial Li2
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ}

/-- The original numerator matrix, explicitly reordered and scaled only by p-units. -/
def parameterNormalizedMatrix (lam : ℚ) (hp4 : 3 < p) :
    Matrix (PrimeBlockIndex p) (PrimeBlockIndex p) ℚ[X] := fun x y =>
  C (primeBlockUnitScale hp4 x * primeBlockUnitScale hp4 y) *
    parameterOriginalNumeratorEntry lam p (by omega)
      ((primeOriginalBlockEquiv hp4).symm x)
      ((primeOriginalBlockEquiv hp4).symm y)

lemma parameterNormalizedMatrix_symm (lam : ℚ) (hp4 : 3 < p) (x y : PrimeBlockIndex p) :
    parameterNormalizedMatrix lam hp4 x y = parameterNormalizedMatrix lam hp4 y x := by
  simp only [parameterNormalizedMatrix, parameterOriginalNumeratorEntry, mul_comm]

lemma parameterNormalizedMatrix_GV_of_original [Fact p.Prime] (lam : ℚ) (hp4 : 3 < p)
    (x y : PrimeBlockIndex p) (r : ℚ)
    (h : GV p (parameterOriginalNumeratorEntry lam p (by omega)
      ((primeOriginalBlockEquiv hp4).symm x)
      ((primeOriginalBlockEquiv hp4).symm y)) r) :
    GV p (parameterNormalizedMatrix lam hp4 x y) r := by
  have hx : VG p (primeBlockUnitScale hp4 x) 0 := by
    right
    rw [(primeBlockUnitScale_unit hp4 x).2]
    norm_num
  have hy : VG p (primeBlockUnitScale hp4 y) 0 := by
    right
    rw [(primeBlockUnitScale_unit hp4 y).2]
    norm_num
  simpa only [parameterNormalizedMatrix, zero_add] using! GV.C_mul (hx.mul hy) h


end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.parameterNormalizedMatrix_GV_of_original

end

section
open Polynomial Li2 Li2Unified.LambdaLift
namespace Li2Unified.Proofs.PrimeEdge
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem norm_le_one_of_integral_near (x : ℤ_[p]) (q : ℚ_[p])
    (h : ‖(x:ℚ_[p])-q‖ ≤ ‖(p:ℚ_[p])‖) : ‖q‖ ≤ 1 := by
  have he : q = (x:ℚ_[p])-((x:ℚ_[p])-q) := by ring
  rw [he]
  rw [sub_eq_add_neg]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  rw [norm_neg]
  exact max_le (PadicInt.norm_le_one x) (h.trans (PadicInt.norm_le_one (p:ℤ_[p])))

theorem zeroShapeUValue_norm_le_one (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 5) :
    ‖(zeroShapeUValue lam k : ℚ_[p])‖ ≤ 1 := by
  have h := parameterZeroShape_U_value_norm lam hu hone hferm hp4 k
  dsimp only at h
  exact norm_le_one_of_integral_near _ _ h

theorem lowShapeVValue_norm_le_one (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 3) :
    ‖(lowShapeVValue lam k : ℚ_[p])‖ ≤ 1 := by
  have h := parameterLowShape_V_value_norm lam hu hone hferm hp4 k
  dsimp only at h
  exact norm_le_one_of_integral_near _ _ h

theorem highShapeVValue_norm_le_one (lam : ℚ)
    (hu : lam ≠ 0 ∧ padicValRat p lam = 0)
    (hone : 1-lam ≠ 0 ∧ padicValRat p (1-lam) = 0)
    (hferm : VG p (lam^p-lam) 1) (hp4 : 3 < p) (k : Fin 3) :
    ‖(highShapeVValue lam k : ℚ_[p])‖ ≤ 1 := by
  have h := parameterHighShape_V_value_norm lam hu hone hferm hp4 k
  dsimp only at h
  exact norm_le_one_of_integral_near _ _ h

end
end Li2Unified.Proofs.PrimeEdge
#print axioms Li2Unified.Proofs.PrimeEdge.lowShapeVValue_norm_le_one

end


end
