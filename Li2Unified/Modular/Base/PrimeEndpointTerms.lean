module
public import Li2Unified.Modular.Base.PrimeAffineInterval

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology Real
namespace Li2.PrimeSums
noncomputable section

lemma log_scaled_div_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log (c*x)/x) atTop (𝓝 0) := by
  have hbase : Tendsto (fun y : ℝ => Real.log y/y) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using!
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hs : Tendsto (fun x : ℝ => c*x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have h := (hbase.comp hs).const_mul c
  have he : (fun x : ℝ => c*(Real.log (c*x)/(c*x))) =ᶠ[atTop]
      (fun x : ℝ => Real.log (c*x)/x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hc.ne', hx.ne']
  simpa only [mul_zero] using! (tendsto_congr' he).mp h

def endpointTerm (α β c x : ℝ) : ℝ :=
  if (⌊c*x⌋₊ : ℝ) = c*x then
    (α*(⌊c*x⌋₊ : ℝ)+β*x)*cPrime ⌊c*x⌋₊
  else 0

lemma endpointTerm_div_eq (α β c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    endpointTerm α β c x/x^2 =
      if (⌊c*x⌋₊).Prime ∧ (⌊c*x⌋₊ : ℝ) = c*x then
        (α*c+β)*(Real.log (c*x)/x)
      else 0 := by
  by_cases he : (⌊c*x⌋₊ : ℝ) = c*x
  · by_cases hp : (⌊c*x⌋₊).Prime
    · simp [endpointTerm, cPrime, he, hp] <;> field_simp [hx] <;> ring
    · simp [endpointTerm, cPrime, he, hp]
  · simp [endpointTerm, he]

theorem endpointTerm_tendsto_zero (α β : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => endpointTerm α β c x/x^2) atTop (𝓝 0) := by
  have hmain : Tendsto (fun x : ℝ => (α*c+β)*(Real.log (c*x)/x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using! (log_scaled_div_tendsto_zero hc).const_mul (α*c+β)
  have hmasked : Tendsto
      (fun x : ℝ => if (⌊c*x⌋₊).Prime ∧ (⌊c*x⌋₊ : ℝ) = c*x then
        (α*c+β)*(Real.log (c*x)/x) else 0) atTop (𝓝 0) :=
    Filter.Tendsto.if' hmain tendsto_const_nhds
  apply (tendsto_congr' ?_).mp hmasked
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (endpointTerm_div_eq α β c hx.ne').symm

theorem endpointTerm_nat_tendsto_zero (α β : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => endpointTerm α β c (n : ℝ)/(n : ℝ)^2) atTop (𝓝 0) :=
  (endpointTerm_tendsto_zero α β hc).comp tendsto_natCast_atTop_atTop

theorem sum_endpointTerm_nat_tendsto_zero {ι : Type*} (s : Finset ι)
    (α β c : ι → ℝ) (hc : ∀ i ∈ s, 0 < c i) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ s, endpointTerm (α i) (β i) (c i) (n : ℝ))/(n : ℝ)^2)
      atTop (𝓝 0) := by
  simp_rw [Finset.sum_div]
  simpa only [Finset.sum_const_zero] using!
    tendsto_finset_sum s (fun i hi => endpointTerm_nat_tendsto_zero (α i) (β i) (hc i hi))

end
end Li2.PrimeSums

end
