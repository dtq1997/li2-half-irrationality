module
public import Li2Unified.Modular.Base.RestrictedPoles

set_option backward.privateInPublic true

@[expose] public section

/-! Multiplication of a finite simple-pole expression by a restricted series.
The regular correction is built from convergent integral divided differences. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma polynomial_coe_finset_sum {κ : Type*} (s : Finset κ) (f : κ → (ℤ_[p])[X]) :
    ((∑ i ∈ s, f i : (ℤ_[p])[X]) : PowerSeries ℤ_[p]) =
      ∑ i ∈ s, (f i : PowerSeries ℤ_[p]) :=
  map_sum Polynomial.coeToPowerSeries.ringHom f s

lemma restricted_finset_sum {κ : Type*} (s : Finset κ)
    (f : κ → PowerSeries ℤ_[p]) (hf : ∀ i ∈ s, PowerSeries.IsRestricted 1 (f i)) :
    PowerSeries.IsRestricted 1 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (PowerSeries.isRestricted_zero (c := 1))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PowerSeries.isRestricted.add 1 (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

def integralPoleMulRegular (c : ι → ℤ_[p]) (g f : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) :
    PowerSeries ℤ_[p] :=
  g*f + ∑ i, PowerSeries.C (r i)*restrictedDivDiff (c i) g

def integralPoleMulResidue (c : ι → ℤ_[p]) (g : PowerSeries ℤ_[p]) (r : ι → ℤ_[p]) :
    ι → ℤ_[p] := fun i => r i*restrictedEval (c i) g

theorem integralPoleMulRegular_isRestricted (c : ι → ℤ_[p])
    (g f : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g)
    (hf : PowerSeries.IsRestricted 1 f) (r : ι → ℤ_[p]) :
    PowerSeries.IsRestricted 1 (integralPoleMulRegular c g f r) := by
  apply PowerSeries.isRestricted.add 1 (PowerSeries.isRestricted.mul 1 hg hf)
  apply restricted_finset_sum
  intro i _
  exact PowerSeries.isRestricted.mul 1 (PowerSeries.isRestricted_C 1 _)
    (restrictedDivDiff_isRestricted _ g hg)

lemma integralPoleDivDiff_identity (c : ι → ℤ_[p])
    (g : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : ι → ℤ_[p]) (i : ι) :
    (integralPoleDenominator c : PowerSeries ℤ_[p])*
        (PowerSeries.C (r i)*restrictedDivDiff (c i) g) +
      PowerSeries.C (r i*restrictedEval (c i) g)*
        (integralPoleCofactor c i : PowerSeries ℤ_[p]) =
      g*(PowerSeries.C (r i)*(integralPoleCofactor c i : PowerSeries ℤ_[p])) := by
  rw [integralPoleDenominator_factor c i]
  simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C,
    map_mul]
  have h := restrictedDivDiff_identity (c i) g hg
  calc
    _ = PowerSeries.C (r i)*(integralPoleCofactor c i : PowerSeries ℤ_[p])*
        ((PowerSeries.X-PowerSeries.C (c i))*restrictedDivDiff (c i) g +
          PowerSeries.C (restrictedEval (c i) g)) := by ring
    _ = _ := by rw [h]; ring

theorem integralPoleNumerator_mul (c : ι → ℤ_[p])
    (g f : PowerSeries ℤ_[p]) (hg : PowerSeries.IsRestricted 1 g) (r : ι → ℤ_[p]) :
    integralPoleNumerator c (integralPoleMulRegular c g f r) (integralPoleMulResidue c g r) =
      g*integralPoleNumerator c f r := by
  unfold integralPoleNumerator integralPoleMulRegular integralPoleMulResidue
  simp only [polynomial_coe_finset_sum, Polynomial.coe_mul, Polynomial.coe_C]
  rw [mul_add, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl (fun i _ => integralPoleDivDiff_identity c g hg r i)

end
end Li2

end
