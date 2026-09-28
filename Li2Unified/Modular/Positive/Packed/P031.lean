module
public import Li2Unified.Modular.Positive.Packed.P029
public import Li2Unified.Modular.Positive.Packed.P025

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Finset
open scoped BigOperators

/-- All reciprocal cells from A=1 through N concatenate to one interval. -/
theorem profileWindowCells_partition (N n : ℕ) (hN : 1 ≤ N) (f : ℕ → ℝ) :
    (∑ A ∈ Finset.Ico (1:ℕ) (N+1),
      ∑ p ∈ Finset.Ioc
        ⌊((1:ℝ)/((A:ℝ)+1))*(n:ℝ)⌋₊
        ⌊((1:ℝ)/(A:ℝ))*(n:ℝ)⌋₊, f p) =
      ∑ p ∈ Finset.Ioc ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ n, f p := by
  induction N, hN using Nat.le_induction with
  | base =>
    norm_num
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N+1), ih]
    have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hN1 : (0:ℝ) < (N:ℝ)+1 := by exact_mod_cast (by omega : 0 < N+1)
    have hN2 : (0:ℝ) < (N:ℝ)+2 := by linarith
    have hrec : (1:ℝ)/((N:ℝ)+2) ≤ 1/((N:ℝ)+1) :=
      one_div_le_one_div_of_le hN1 (by linarith)
    have h01 :
        ⌊((1:ℝ)/((N:ℝ)+2))*(n:ℝ)⌋₊ ≤
          ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_right hrec hnR)
    have hrec1 : (1:ℝ)/((N:ℝ)+1) ≤ 1 := by
      have hNge : (1:ℝ) ≤ (N:ℝ)+1 := by
        have := Nat.cast_nonneg (α := ℝ) N
        linarith
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
        hNge
      simpa using h
    have h12 : ⌊((1:ℝ)/((N:ℝ)+1))*(n:ℝ)⌋₊ ≤ n := by
      have h := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hrec1 hnR)
      simpa using h
    have hconcat := Finset.sum_Ioc_consecutive f h01 h12
    rw [add_comm]
    convert hconcat using 1 <;> push_cast <;> ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profileWindowCells_partition

end

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation

/-- Interior of the first sixth of one reciprocal profile cell. -/
theorem profile_piece_zero (A : ℕ) (x : ℝ) (_hA : 1 ≤ A) (hx : 0 < x)
    (hlo : (A:ℝ) < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/4) :
    profile x = (2*(A:ℝ)^2+3*(A:ℝ))*x-2*(A:ℝ)-5 := by
  have hfloor (m : ℕ) (y : ℝ) (hlo' : (m:ℝ) ≤ y)
      (hhi' : y < (m:ℝ)+1) :
      (⌊y⌋ : ℝ) = (m:ℝ) := by
    have h : ⌊y⌋ = (m:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hlo'
      · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hhi'
    exact_mod_cast h
  have h1lo : (A:ℝ) ≤ (1:ℝ)/x := by simpa only [one_div] using hlo.le
  have h1hi : (1:ℝ)/x < (A:ℝ)+1 := by
    rw [one_div]
    linarith only [hhi]
  have h2lo : ((2*A:ℕ):ℝ) ≤ (2:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hlo]
  have h2hi : (2:ℝ)/x < ((2*A:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hhi]
  have h4lo : ((4*A:ℕ):ℝ) ≤ (4:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hlo]
  have h4hi : (4:ℝ)/x < ((4*A:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hhi]
  have hf1 := hfloor A (1/x) h1lo h1hi
  have hf2 := hfloor (2*A) (2/x) h2lo h2hi
  have hf4 := hfloor (4*A) (4/x) h4lo h4hi
  have hAx : (A:ℝ)*x < 1 := by
    have h := mul_lt_mul_of_pos_right hlo hx
    simpa only [inv_mul_cancel₀ hx.ne'] using h
  have hmin : min (1-(A:ℝ)*x) (4-((4*A:ℕ):ℝ)*x) = 1-(A:ℝ)*x := by
    apply min_eq_left
    push_cast
    nlinarith only [hAx]
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

/-- The three floors on any subcell with `lo < 1/x - A < hi`. -/
private theorem profile_floors_on_theta (A j b : ℕ) (x lo hi : ℝ)
    (hθlo : (A:ℝ)+lo < x⁻¹) (hθhi : x⁻¹ < (A:ℝ)+hi)
    (hlo0 : 0 ≤ lo) (hhi1 : hi ≤ 1)
    (hbLo : (b:ℝ) ≤ 2*lo) (hbHi : 2*hi ≤ (b:ℝ)+1)
    (hjLo : (j:ℝ) ≤ 4*lo) (hjHi : 4*hi ≤ (j:ℝ)+1) :
    (⌊(1:ℝ)/x⌋ : ℝ) = (A:ℝ) ∧
      (⌊(2:ℝ)/x⌋ : ℝ) = ((2*A+b:ℕ):ℝ) ∧
      (⌊(4:ℝ)/x⌋ : ℝ) = ((4*A+j:ℕ):ℝ) := by
  have hfloor (m : ℕ) (y : ℝ) (hlo' : (m:ℝ) ≤ y)
      (hhi' : y < (m:ℝ)+1) : (⌊y⌋ : ℝ) = (m:ℝ) := by
    have h : ⌊y⌋ = (m:ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact_mod_cast hlo'
      · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hhi'
    exact_mod_cast h
  have h1lo : (A:ℝ) ≤ (1:ℝ)/x := by
    rw [one_div]
    linarith only [hθlo, hlo0]
  have h1hi : (1:ℝ)/x < (A:ℝ)+1 := by
    rw [one_div]
    linarith only [hθhi, hhi1]
  have h2lo : ((2*A+b:ℕ):ℝ) ≤ (2:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθlo, hbLo]
  have h2hi : (2:ℝ)/x < ((2*A+b:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθhi, hbHi]
  have h4lo : ((4*A+j:ℕ):ℝ) ≤ (4:ℝ)/x := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθlo, hjLo]
  have h4hi : (4:ℝ)/x < ((4*A+j:ℕ):ℝ)+1 := by
    rw [div_eq_mul_inv]
    push_cast
    linarith only [hθhi, hjHi]
  exact ⟨hfloor A (1/x) h1lo h1hi,
    hfloor (2*A+b) (2/x) h2lo h2hi,
    hfloor (4*A+j) (4/x) h4lo h4hi⟩

private theorem profile_min_first (A j : ℕ) (x : ℝ) (hx : 0 < x)
    (hθ : (A:ℝ)+(j:ℝ)/3 < x⁻¹) :
    min (1-(A:ℝ)*x) (4-((4*A+j:ℕ):ℝ)*x) = 1-(A:ℝ)*x := by
  have hm := mul_lt_mul_of_pos_right hθ hx
  have hb : ((A:ℝ)+(j:ℝ)/3)*x < 1 := by
    simpa only [inv_mul_cancel₀ hx.ne'] using hm
  apply min_eq_left
  push_cast
  nlinarith only [hb]

private theorem profile_min_second (A j : ℕ) (x : ℝ) (hx : 0 < x)
    (hθ : x⁻¹ < (A:ℝ)+(j:ℝ)/3) :
    min (1-(A:ℝ)*x) (4-((4*A+j:ℕ):ℝ)*x) =
      4-((4*A+j:ℕ):ℝ)*x := by
  have hm := mul_lt_mul_of_pos_right hθ hx
  have hb : 1 < ((A:ℝ)+(j:ℝ)/3)*x := by
    simpa only [inv_mul_cancel₀ hx.ne'] using hm
  apply min_eq_right
  push_cast
  nlinarith only [hb]

theorem profile_piece_one (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/4 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/3) :
    profile x = (2*(A:ℝ)^2-(A:ℝ)-1)*x-2*(A:ℝ)+1 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 1 0 x (1/4) (1/3) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second A 1 x hx (by simpa only [Nat.cast_one] using hhi)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_two (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/3 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/2) :
    profile x = (2*(A:ℝ)^2+2*(A:ℝ))*x-2*(A:ℝ)-2 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 1 0 x (1/3) (1/2) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first A 1 x hx (by simpa only [Nat.cast_one] using hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_three (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/2 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+2/3) :
    profile x = (2*(A:ℝ)^2+2*(A:ℝ))*x-2*(A:ℝ) := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 2 1 x (1/2) (2/3) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second A 2 x hx (by norm_num at hhi ⊢; exact hhi)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_four (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+2/3 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+3/4) :
    profile x = (2*(A:ℝ)^2+5*(A:ℝ)+2)*x-2*(A:ℝ)-3 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 2 1 x (2/3) (3/4) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first A 2 x hx (by norm_num at hlo ⊢; exact hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_five (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+3/4 < x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1) :
    profile x = (2*(A:ℝ)^2+(A:ℝ)-1)*x-2*(A:ℝ)+3 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_on_theta A 3 1 x (3/4) 1 hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second A 3 x hx (by norm_num at hhi ⊢; exact hhi)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_zero
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_one
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_two
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_three
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_four
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_five

end


end
