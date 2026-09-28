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

end
end Li2.PrimeSums

end
