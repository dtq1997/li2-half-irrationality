module
public import Li2Unified.Modular.Base.PrimeThetaInterval
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology Asymptotics
namespace Li2.PrimeSums
noncomputable section

lemma psi_sub_theta_isLittleO_id :
    (fun x : ℝ => Chebyshev.psi x-Chebyshev.theta x) =o[atTop] _root_.id := by
  have hO : (fun x : ℝ => Chebyshev.psi x-Chebyshev.theta x) =O[atTop]
      (fun x : ℝ => 2*Real.sqrt x*Real.log x) := by
    rw [isBigO_iff']
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hnonneg : 0 ≤ 2*Real.sqrt x*Real.log x :=
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg x))
        (Real.log_nonneg hx)
    simp only [Real.norm_eq_abs, one_mul, abs_of_nonneg hnonneg]
    exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  exact hO.trans_isLittleO (by
    simpa only [mul_assoc] using! Li2.PNT.isLittleO_sqrt_mul_log.const_mul_left (2 : ℝ))

lemma psi_sub_theta_scaled_nat_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (Chebyshev.psi (c*(n : ℝ))-Chebyshev.theta (c*(n : ℝ)))/(n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun n : ℕ => c*(n : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ =>
      c*((Chebyshev.psi (c*(n : ℝ))-Chebyshev.theta (c*(n : ℝ)))/(c*(n : ℝ))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using!
      (psi_sub_theta_isLittleO_id.tendsto_div_nhds_zero.comp hs).const_mul c
  apply (tendsto_congr' ?_).mp h
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hc.ne', hn0] <;> ring

/-- Logarithmic weight of powers p^k with k≥2, restricted to P. -/
def primePowerExcess (D : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, ((((Nat.log p D-1 : ℕ) : ℝ))*Real.log (p : ℝ))

lemma primePowerExcess_nonneg (D : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) : 0 ≤ primePowerExcess D P := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))

lemma primePowerExcess_mono (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D E : ℕ} (hDE : D ≤ E) : primePowerExcess D P ≤ primePowerExcess E P := by
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Nat.sub_le_sub_right (Nat.log_mono_right (b := p) hDE) 1)
  · exact Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)

lemma primePowerExcess_le_psi_sub_theta {D : ℕ} (hD : 0 < D)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    primePowerExcess D P ≤ Chebyshev.psi (D : ℝ)-Chebyshev.theta (D : ℝ) := by
  classical
  let T : Finset (Σ _ : ℕ, ℕ) := P.sigma (fun p => Finset.Icc 2 (Nat.log p D))
  have hinj : Set.InjOn (fun z : Σ _ : ℕ, ℕ => z.1^z.2) (T : Set (Σ _ : ℕ, ℕ)) := by
    intro x hx y hy hxy
    rcases x with ⟨p, k⟩
    rcases y with ⟨q, l⟩
    obtain ⟨hp, hk⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hq, hl⟩ := Finset.mem_sigma.mp hy
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    change p^k = q^l at hxy
    obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj' (hP p hp) (hP q hq)
      (by omega : k ≠ 0) (by omega : l ≠ 0) hxy
    rfl
  have hsub : T.image (fun z => z.1^z.2) ⊆
      (Finset.Ioc 0 D).filter (fun m : ℕ => ¬m.Prime) := by
    intro m hm
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hzP, hzK⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hk2, hkL⟩ := Finset.mem_Icc.mp hzK
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, Nat.Prime.not_prime_pow hk2⟩
    · exact pow_pos (hP z.1 hzP).pos z.2
    · exact Nat.pow_le_of_le_log hD.ne' hkL
  have hsum : (∑ z ∈ T, (ArithmeticFunction.vonMangoldt (z.1^z.2))) =
      primePowerExcess D P := by
    unfold primePowerExcess
    dsimp [T]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro p hp
    calc
      (∑ k ∈ Finset.Icc 2 (Nat.log p D), (ArithmeticFunction.vonMangoldt (p^k))) =
          ∑ k ∈ Finset.Icc 2 (Nat.log p D), (Real.log (p : ℝ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]
      _ = ((Nat.log p D-1 : ℕ) : ℝ)*Real.log (p : ℝ) := by
        simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        rw [show Nat.log p D+1-2 = Nat.log p D-1 by omega]
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  calc
    primePowerExcess D P = ∑ z ∈ T, (ArithmeticFunction.vonMangoldt (z.1^z.2)) := hsum.symm
    _ = ∑ m ∈ T.image (fun z => z.1^z.2), (ArithmeticFunction.vonMangoldt m) :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ m ∈ (Finset.Ioc 0 D).filter (fun m : ℕ => ¬m.Prime),
        (ArithmeticFunction.vonMangoldt m) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m hm hnot => ArithmeticFunction.vonMangoldt_nonneg)

theorem primePowerExcess_seven_sub_two_tendsto_zero
    (P : ℕ → Finset ℕ) (hP : ∀ n p, p ∈ P n → p.Prime) :
    Tendsto (fun n : ℕ => primePowerExcess (7*n-2) (P n)/(n : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (psi_sub_theta_scaled_nat_tendsto_zero (c := (7 : ℝ)) (by norm_num)) ?_ ?_
  · exact Filter.Eventually.of_forall (fun n =>
      div_nonneg (primePowerExcess_nonneg (7*n-2) (P n) (hP n)) (Nat.cast_nonneg n))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hs := (primePowerExcess_mono (P n) (hP n) (Nat.sub_le (7*n) 2)).trans
      (primePowerExcess_le_psi_sub_theta (by omega : 0 < 7*n) (P n) (hP n))
    have hs' : primePowerExcess (7*n-2) (P n) ≤
        Chebyshev.psi (7*(n : ℝ))-Chebyshev.theta (7*(n : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using! hs
    exact div_le_div_of_nonneg_right hs' (Nat.cast_nonneg n)

end
end Li2.PrimeSums

end
