module
public import Li2Unified.Modular.Positive.Packed.P025
public import Li2Unified.Modular.Positive.Packed.P043

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.ParameterFamily Li2Unified.Instances.PosHalf
open Li2Unified.Stage0.HermitePreparation
open Filter Finset
open scoped BigOperators

/-- A reciprocal cutoff lies above the square-root threshold once `n` is large. -/
private theorem square_window_of_cutoff (N n p : ℕ)
    (hn : 4 * (N + 1) ^ 2 ≤ n)
    (hp : ⌊((1:ℝ) / ((N:ℝ) + 1)) * (n:ℝ)⌋₊ < p) :
    4 * n < p * p := by
  have hd : (0:ℝ) < (N:ℝ) + 1 := by positivity
  have hnonneg : (0:ℝ) ≤ ((1:ℝ) / ((N:ℝ) + 1)) * (n:ℝ) := by positivity
  have hfloor : ((1:ℝ) / ((N:ℝ) + 1)) * (n:ℝ) < (p:ℝ) :=
    (Nat.floor_lt hnonneg).mp hp
  have hnp : (n:ℝ) < ((N:ℝ) + 1) * (p:ℝ) := by
    have hh : (n:ℝ) < (p:ℝ) * ((N:ℝ) + 1) :=
      (div_lt_iff₀ hd).mp (by
        simpa only [one_div, one_mul, div_eq_mul_inv, mul_comm] using hfloor)
    nlinarith
  have hnR : (4:ℝ) * ((N:ℝ) + 1) ^ 2 ≤ (n:ℝ) := by
    exact_mod_cast hn
  have hp4 : (4:ℝ) * ((N:ℝ) + 1) < (p:ℝ) := by
    by_contra hh
    have hle : (p:ℝ) ≤ 4 * ((N:ℝ) + 1) := le_of_not_gt hh
    have hmul := mul_le_mul_of_nonneg_left hle hd.le
    nlinarith
  have hpp : (0:ℝ) < (p:ℝ) * ((p:ℝ) - 4 * ((N:ℝ) + 1)) := by
    apply mul_pos
    · linarith
    · linarith
  have hsq : (4:ℝ) * (n:ℝ) < (p:ℝ) ^ 2 := by
    nlinarith
  have hsqNat : 4 * n < p ^ 2 := by exact_mod_cast hsq
  simpa only [pow_two] using hsqNat

/-- The two positive-half parameter factors are units at every prime at least five. -/
private theorem posHalf_parameter_units (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (lambda ≠ 0 ∧ padicValRat p lambda = 0) ∧
      (1-lambda ≠ 0 ∧ padicValRat p (1-lambda) = 0) := by
  have hp2 : ¬p ∣ 2 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have hp1 : ¬p ∣ 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 1) hd
    omega
  rw [lambda_eq_inverse]
  exact ⟨inverseParameter_unit 2 (by norm_num) hp2,
    inverseParameter_one_sub_unit 2 (by norm_num) hp2 (by simpa using hp1)⟩

/-- The full `ε` medium-prime rate follows by choosing one finite reciprocal
cutoff after `ε`. The actual Gram estimate applies above the finite cutoff. -/
theorem posHalf_medium_eventually_actual (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Instances.PosHalf.Qtilde n ≠ 0 →
        ((-523/840:ℝ)-ε)*(n:ℝ)^2 ≤
          ∑ p ∈ (Finset.range (n+1)).filter (fun p => p.Prime ∧ 5 ≤ p),
            ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ) := by
  obtain ⟨N, hN, hδ0raw, hδ1raw, hδbudgetRaw⟩ :=
    exists_finite_cutoff ε hε
  let δ : ℝ := 1/((N:ℝ)+1)
  have hδ0 : 0 < δ := by
    simpa only [δ, Nat.cast_add, Nat.cast_one] using hδ0raw
  have hδ1 : δ ≤ 1 := by
    simpa only [δ, Nat.cast_add, Nat.cast_one] using hδ1raw
  have hδbudget : 4*δ < ε/2 := by
    simpa only [δ, Nat.cast_add, Nat.cast_one, mul_one_div] using hδbudgetRaw
  have hε4 : 0 < ε/4 := by linarith
  have hsmall := posHalf_smallTail_eventually_delta δ (ε/4)
    hδ0 hδ1 hε4
  have hmedium := parameter_mediumN_eventually lambda N hN (ε/4) hε4
  filter_upwards [hsmall, hmedium,
    eventually_ge_atTop (4*(N+1)),
    eventually_ge_atTop (4*(N+1)^2)] with n hs hm hn hnSq
  intro hne
  let c := ⌊δ*(n:ℝ)⌋₊
  have hc4 : 4 ≤ c := by
    apply (Nat.le_floor_iff (mul_nonneg hδ0.le (Nat.cast_nonneg n))).mpr
    have hnR : (4:ℝ)*((N:ℝ)+1) ≤ (n:ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hn
      push_cast at this
      nlinarith
    dsimp [δ]
    have hden : (0:ℝ) < (N:ℝ)+1 := by positivity
    calc
      (4:ℝ) = 4*((N:ℝ)+1)/((N:ℝ)+1) := by field_simp
      _ ≤ ((n:ℝ))/((N:ℝ)+1) :=
        div_le_div_of_nonneg_right hnR hden.le
      _ = (1/((N:ℝ)+1))*(n:ℝ) := by ring
  have hcn : c ≤ n := by
    have hle : δ*(n:ℝ) ≤ (n:ℝ) := by
      have hnR : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
      nlinarith [hδ1]
    have := Nat.floor_le_floor hle
    simpa only [Nat.floor_natCast] using this
  let f : ℕ → ℝ := fun p =>
    ((-padicValRat p (dtilde lambda n) : ℤ) : ℝ)*Real.log (p:ℝ)
  have hpart := medium_prime_two_interval_partition f n c hc4 hcn
  have hsmallEq :
      (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) =
      ∑ p ∈ smallTailPrimes δ n,
        if p.Prime then f p else 0 := by
    change (∑ p ∈ Finset.Ioc 4 c, if p.Prime then f p else 0) =
      ∑ p ∈ (Finset.Ioc 4 c).filter Nat.Prime,
        if p.Prime then f p else 0
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> simp [hp]
  have hgramN : ∀ p ∈ Finset.Ioc c n, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      Li2.GV p (binomGram lambda n).det (normalizedDetLower n p) := by
    intro p hpI hp
    obtain ⟨hpc, hpn⟩ := Finset.mem_Ioc.mp hpI
    have hp5 : 5 ≤ p := by omega
    have hcut : ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ < p := by
      simpa only [c, δ] using hpc
    have hsq : 4*n < p*p := square_window_of_cutoff N n p hnSq hcut
    letI : Fact p.Prime := ⟨hp⟩
    exact actual_binomGram lambda n p (by norm_num [lambda]) hp5 hpn hsq
      (posHalf_parameter_units p hp5)
  have hs' := hs hne
  have hm' := hm (by omega : 0 < n)
    (by simpa only [Instances.PosHalf.Qtilde] using hne) hgramN
  have hbudget : (-523/840:ℝ)-ε ≤
      ((-523/840:ℝ)+(2/3:ℝ)/((N+1:ℕ):ℝ)^2-ε/4) +
      (-4*δ-ε/4) := by
    have hcorr : (0:ℝ) ≤ (2/3:ℝ)/((N+1:ℕ):ℝ)^2 := by positivity
    linarith
  have hbudgetN := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (n:ℝ))
  rw [hpart, hsmallEq]
  dsimp only [f] at hs' hm' ⊢
  linarith

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.square_window_of_cutoff
#print axioms Li2Unified.Proofs.Arithmetic.posHalf_medium_eventually_actual

end


end
