module
public import Li2Unified.Modular.Base.Valuation

set_option backward.privateInPublic true

@[expose] public section

/-! Perturbation bounds for determinants, with rational row/column weights. -/
open Polynomial
open scoped BigOperators
namespace Li2
variable {p : ℕ} [Fact p.Prime]

lemma GV.prod_sub_prod {ι : Type*} (s : Finset ι) {F G : ι → ℚ[X]}
    {r : ι → ℚ} {δ : ℚ}
    (hF : ∀ i ∈ s, GV p (F i) (r i))
    (hG : ∀ i ∈ s, GV p (G i) (r i))
    (hFG : ∀ i ∈ s, GV p (F i-G i) (r i+δ)) :
    GV p ((∏ i ∈ s, F i) - ∏ i ∈ s, G i) ((∑ i ∈ s, r i)+δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GV.zero (p := p) δ
  | insert a s ha ih =>
    have hFs := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hGs := fun i hi => hG i (Finset.mem_insert_of_mem hi)
    have hFGs := fun i hi => hFG i (Finset.mem_insert_of_mem hi)
    have h1 := (hFG a (Finset.mem_insert_self _ _)).mul (GV.prod s hFs)
    have h2 := (hG a (Finset.mem_insert_self _ _)).mul (ih hFs hGs hFGs)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have he : F a * (∏ i ∈ s, F i) - G a * (∏ i ∈ s, G i) =
        (F a-G a) * (∏ i ∈ s, F i) +
          G a * ((∏ i ∈ s, F i) - ∏ i ∈ s, G i) := by ring
    rw [he]
    apply GV.add
    · convert h1 using 1 <;> ring
    · convert h2 using 1 <;> ring

theorem det_sub_GV {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℚ[X]) (ρ κ : ι → ℚ) (δ : ℚ)
    (hM : ∀ i j, GV p (M i j) (ρ i+κ j))
    (hN : ∀ i j, GV p (N i j) (ρ i+κ j))
    (hMN : ∀ i j, GV p (M i j-N i j) (ρ i+κ j+δ)) :
    GV p (M.det-N.det) ((∑ i, ρ i)+(∑ j, κ j)+δ) := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  apply GV.sum
  intro σ _
  have h := GV.prod_sub_prod Finset.univ
    (fun i _ => hM (σ i) i) (fun i _ => hN (σ i) i) (fun i _ => hMN (σ i) i)
  have he : (∑ i, (ρ (σ i)+κ i))+δ = (∑ i, ρ i)+(∑ i, κ i)+δ := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ ρ]
  rw [he] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul, one_smul]
    exact h
  · simpa only [hs, Units.neg_smul, one_smul, neg_sub_neg, neg_sub] using h.neg

lemma VG.round_half {q : ℚ} (r : ℤ) (h : VG p q ((r:ℚ)+1/2)) :
    VG p q ((r:ℚ)+1) := by
  rcases h with h | h
  · exact Or.inl h
  right
  have ht : (r:ℚ) < padicValRat p q := by linarith
  have hi : r < padicValRat p q := by exact_mod_cast ht
  exact_mod_cast (Int.add_one_le_iff.mpr hi)

end Li2

end
