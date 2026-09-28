module
public import Li2Unified.Modular.Base.PrimeWeightedAbel

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology Set Real
namespace Li2.PrimeSums
noncomputable section

lemma wsum_scaled_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => wsum (a*x) (b*x)/x^2) atTop (𝓝 ((b^2-a^2)/2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hb : 0 < b := ha.trans_le hab
  set η := ε/(8*b^2) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨Y0, hY0⟩ := eventually_atTop.mp (theta_eventually_close hη)
  refine ⟨max (Y0/a) 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hxY : Y0/a ≤ x := le_trans (le_max_left _ _) hx
  have hYa : Y0 ≤ a*x := by
    have hh := (div_le_iff₀ ha).mp hxY
    nlinarith only [hh]
  have hax : 0 ≤ a*x := mul_nonneg ha.le hx0.le
  have habx : a*x ≤ b*x := mul_le_mul_of_nonneg_right hab hx0.le
  have hbound := wsum_close hax habx hη.le
    (fun y hy => hY0 y (hYa.trans hy.1))
  rw [Real.dist_eq]
  have he : wsum (a*x) (b*x)/x^2-(b^2-a^2)/2 =
      (wsum (a*x) (b*x)-((b*x)^2-(a*x)^2)/2)/x^2 := by
    field_simp [hx0.ne']
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < x^2),
    div_lt_iff₀ (by positivity : (0 : ℝ) < x^2)]
  calc
    |wsum (a*x) (b*x)-((b*x)^2-(a*x)^2)/2| ≤ 2*η*(b*x)^2 := hbound
    _ = ε*x^2/4 := by
      rw [hηdef]
      field_simp [hb.ne']
      ring
    _ < ε*x^2 := by
      have hh : 0 < ε*x^2 := by positivity
      linarith

def affineSum (α β a b x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊a*x⌋₊ ⌊b*x⌋₊, (α*(k : ℝ)+β*x)*cPrime k

lemma affineSum_eq (α β a b x : ℝ) :
    affineSum α β a b x = α*wsum (a*x) (b*x)+β*x*logSum (a*x) (b*x) := by
  unfold affineSum wsum logSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem affineSum_tendsto (α β : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => affineSum α β a b x/x^2) atTop
      (𝓝 (α*((b^2-a^2)/2)+β*(b-a))) := by
  have h := ((wsum_scaled_tendsto ha hab).const_mul α).add
    ((logSum_scaled_tendsto ha hab).const_mul β)
  have he :
      (fun x : ℝ => α*(wsum (a*x) (b*x)/x^2)+β*(logSum (a*x) (b*x)/x)) =ᶠ[atTop]
      (fun x : ℝ => affineSum α β a b x/x^2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [affineSum_eq]
    field_simp [hx.ne']
  exact (tendsto_congr' he).mp h

theorem affineSum_nat_tendsto (α β : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => affineSum α β a b (n : ℝ)/(n : ℝ)^2) atTop
      (𝓝 (α*((b^2-a^2)/2)+β*(b-a))) :=
  (affineSum_tendsto α β ha hab).comp tendsto_natCast_atTop_atTop

end
end Li2.PrimeSums

end
