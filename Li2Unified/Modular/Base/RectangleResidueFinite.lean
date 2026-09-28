module
public import Li2Unified.Modular.Base.RectangleResidue

set_option backward.privateInPublic true

@[expose] public section

open MeasureTheory
namespace Li2
noncomputable section

lemma rectangleKernel_continuous_horizontal {a : ℝ} {p : ℂ} (ha : a ≠ p.im) :
    Continuous (fun x : ℝ => ((x : ℂ) + (a : ℂ) * Complex.I - p)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro x hx
  have h : a - p.im = 0 := by simpa using congrArg Complex.im hx
  exact ha (sub_eq_zero.mp h)

lemma rectangleKernel_continuous_vertical {a : ℝ} {p : ℂ} (ha : a ≠ p.re) :
    Continuous (fun y : ℝ => ((a : ℂ) + (y : ℂ) * Complex.I - p)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro y hy
  have h : a - p.re = 0 := by simpa using congrArg Complex.re hy
  exact ha (sub_eq_zero.mp h)

theorem boundaryIntegral_finset_simplePoles {ι : Type*} (S : Finset ι)
    (p c : ι → ℂ) (z w : ℂ)
    (hre : ∀ i ∈ S, (p i).re ∈ Set.Ioo z.re w.re)
    (him : ∀ i ∈ S, (p i).im ∈ Set.Ioo z.im w.im) :
    Complex.boundaryIntegral (fun s => ∑ i ∈ S, c i * (s - p i)⁻¹) z w =
      (2 * (Real.pi : ℂ) * Complex.I) * ∑ i ∈ S, c i := by
  classical
  have hb (i : ι) (hi : i ∈ S) : IntervalIntegrable
      (fun x : ℝ => c i * ((x : ℂ) + z.im * Complex.I - p i)⁻¹) volume z.re w.re :=
    ((rectangleKernel_continuous_horizontal (p := p i)
      (ne_of_lt (him i hi).1)).intervalIntegrable _ _).const_mul _
  have ht (i : ι) (hi : i ∈ S) : IntervalIntegrable
      (fun x : ℝ => c i * ((x : ℂ) + w.im * Complex.I - p i)⁻¹) volume z.re w.re :=
    ((rectangleKernel_continuous_horizontal (p := p i)
      (ne_of_gt (him i hi).2)).intervalIntegrable _ _).const_mul _
  have hr (i : ι) (hi : i ∈ S) : IntervalIntegrable
      (fun y : ℝ => c i * (w.re + (y : ℂ) * Complex.I - p i)⁻¹) volume z.im w.im :=
    ((rectangleKernel_continuous_vertical (p := p i)
      (ne_of_gt (hre i hi).2)).intervalIntegrable _ _).const_mul _
  have hl (i : ι) (hi : i ∈ S) : IntervalIntegrable
      (fun y : ℝ => c i * (z.re + (y : ℂ) * Complex.I - p i)⁻¹) volume z.im w.im :=
    ((rectangleKernel_continuous_vertical (p := p i)
      (ne_of_lt (hre i hi).1)).intervalIntegrable _ _).const_mul _
  rw [Complex.boundaryIntegral_finset_sum S
    (fun i s => c i * (s - p i)⁻¹) z w hb ht hr hl]
  calc
    (∑ i ∈ S, Complex.boundaryIntegral (fun s => c i * (s - p i)⁻¹) z w) =
        ∑ i ∈ S, c i * (2 * (Real.pi : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.boundaryIntegral_const_mul,
        Complex.boundaryIntegral_inv_sub_eq_two_pi_I (hre i hi) (him i hi)]
    _ = (2 * (Real.pi : ℂ) * Complex.I) * ∑ i ∈ S, c i := by
      rw [← Finset.sum_mul, mul_comm]

end
end Li2

end
