module
public import Li2Unified.Modular.Positive.Packed.P031

set_option backward.privateInPublic true

@[expose] public section

section
namespace Li2Unified.Proofs.Arithmetic
noncomputable section
open Li2Unified.Stage0.HermitePreparation

/-- The floor values include the left endpoint in θ = 1/x-A. -/
private theorem profile_floors_closed_theta (A j b : ℕ) (x lo hi : ℝ)
    (hθlo : (A:ℝ)+lo ≤ x⁻¹) (hθhi : x⁻¹ < (A:ℝ)+hi)
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
      · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using! hhi'
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

private theorem profile_min_first_closed (A j : ℕ) (x : ℝ) (hx : 0 < x)
    (hθ : (A:ℝ)+(j:ℝ)/3 ≤ x⁻¹) :
    min (1-(A:ℝ)*x) (4-((4*A+j:ℕ):ℝ)*x) = 1-(A:ℝ)*x := by
  have hm := mul_le_mul_of_nonneg_right hθ hx.le
  have hb : ((A:ℝ)+(j:ℝ)/3)*x ≤ 1 := by
    simpa only [inv_mul_cancel₀ hx.ne'] using! hm
  apply min_eq_left
  push_cast
  nlinarith only [hb]

private theorem profile_min_second_closed (A j : ℕ) (x : ℝ) (hx : 0 < x)
    (hθ : x⁻¹ ≤ (A:ℝ)+(j:ℝ)/3) :
    min (1-(A:ℝ)*x) (4-((4*A+j:ℕ):ℝ)*x) =
      4-((4*A+j:ℕ):ℝ)*x := by
  have hm := mul_le_mul_of_nonneg_right hθ hx.le
  have hb : 1 ≤ ((A:ℝ)+(j:ℝ)/3)*x := by
    simpa only [inv_mul_cancel₀ hx.ne'] using! hm
  apply min_eq_right
  push_cast
  nlinarith only [hb]

theorem profile_piece_zero_closed (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ) ≤ x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/4) :
    profile x = (2*(A:ℝ)^2+3*(A:ℝ))*x-2*(A:ℝ)-5 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_closed_theta A 0 0 x 0 (1/4) (by simpa using! hlo) hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first_closed A 0 x hx (by simpa using! hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_one_closed (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/4 ≤ x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/3) :
    profile x = (2*(A:ℝ)^2-(A:ℝ)-1)*x-2*(A:ℝ)+1 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_closed_theta A 1 0 x (1/4) (1/3) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second_closed A 1 x hx (by linarith)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_two_closed (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/3 ≤ x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1/2) :
    profile x = (2*(A:ℝ)^2+2*(A:ℝ))*x-2*(A:ℝ)-2 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_closed_theta A 1 0 x (1/3) (1/2) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first_closed A 1 x hx (by simpa using! hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_three_closed (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+1/2 ≤ x⁻¹) (hhi : x⁻¹ < (A:ℝ)+2/3) :
    profile x = (2*(A:ℝ)^2+2*(A:ℝ))*x-2*(A:ℝ) := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_closed_theta A 2 1 x (1/2) (2/3) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second_closed A 2 x hx (by norm_num at hhi ⊢; exact hhi.le)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_four_closed (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+2/3 ≤ x⁻¹) (hhi : x⁻¹ < (A:ℝ)+3/4) :
    profile x = (2*(A:ℝ)^2+5*(A:ℝ)+2)*x-2*(A:ℝ)-3 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_closed_theta A 2 1 x (2/3) (3/4) hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_first_closed A 2 x hx (by norm_num at hlo ⊢; exact hlo)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

theorem profile_piece_five_closed (A : ℕ) (x : ℝ) (hx : 0 < x)
    (hlo : (A:ℝ)+3/4 ≤ x⁻¹) (hhi : x⁻¹ < (A:ℝ)+1) :
    profile x = (2*(A:ℝ)^2+(A:ℝ)-1)*x-2*(A:ℝ)+3 := by
  obtain ⟨hf1, hf2, hf4⟩ :=
    profile_floors_closed_theta A 3 1 x (3/4) 1 hlo hhi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have hmin := profile_min_second_closed A 3 x hx (by norm_num at hhi ⊢; exact hhi.le)
  dsimp [profile]
  rw [hf1, hf2, hf4, hmin]
  push_cast
  ring

end
end Li2Unified.Proofs.Arithmetic

#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_zero_closed
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_one_closed
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_two_closed
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_three_closed
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_four_closed
#print axioms Li2Unified.Proofs.Arithmetic.profile_piece_five_closed

end


end
