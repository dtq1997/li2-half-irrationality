module
public import Li2Unified.Modular.Base.RestrictedPoleBounds
public import Li2Unified.Modular.Base.ParameterPoleValues

set_option backward.privateInPublic true

@[expose] public section

/-! The bounded U/V extensions with the actual z=(-1/2)^p parameter,
on the four simple poles u=0,-1,-2,-3. Y is the polynomial variable. -/
open Polynomial Finset
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma restrictedPoleFunctional_regular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X]) (f : PowerSeries ℤ_[p]) :
    restrictedPoleFunctional μ w f 0 = C (restrictedMoment μ f) := by
  simp [restrictedPoleFunctional]

lemma restrictedPoleFunctional_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℕ → ℤ_[p]) (w : ι → (ℤ_[p])[X]) (j : ι) :
    restrictedPoleFunctional μ w 0 (Pi.single j 1) = w j := by
  simp [restrictedPoleFunctional, restrictedMoment, Pi.single_apply]

def primePoleCenters (p : ℕ) [Fact p.Prime] : Fin 4 → ℤ_[p] := fun i => -(i.val:ℤ_[p])

lemma primePoleCenters_injective : Function.Injective (primePoleCenters p) := by
  intro i j h
  apply Fin.ext
  have he : (i.val:ℤ_[p]) = (j.val:ℤ_[p]) := neg_injective h
  exact_mod_cast he

def primePoleU (hp4 : 3 < p) (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) : (ℤ_[p])[X] :=
  restrictedPoleFunctional
    (fun n => (n+1:ℕ)*integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral (by omega) (by omega)) n)
    (fun j : Fin 4 => primeUPole (by omega) j.val (by omega)) f r

def primePoleV (hp4 : 3 < p) (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) : (ℤ_[p])[X] :=
  restrictedPoleFunctional
    (derivativeMoments (integralParameterMoment (primeParameter p)
      (primeParameter_moment_integral (by omega) (by omega))))
    (fun j : Fin 4 => primeVPole (by omega) j.val (by omega)) f r

theorem primePoleU_regular (hp4 : 3 < p) (f : PowerSeries ℤ_[p]) :
    primePoleU hp4 f 0 = C (restrictedU
      (integralParameterMoment (primeParameter p)
        (primeParameter_moment_integral (by omega) (by omega))) f) :=
  restrictedPoleFunctional_regular _ _ _

theorem primePoleV_regular (hp4 : 3 < p) (f : PowerSeries ℤ_[p]) :
    primePoleV hp4 f 0 = C (restrictedV
      (integralParameterMoment (primeParameter p)
        (primeParameter_moment_integral (by omega) (by omega))) f) :=
  restrictedPoleFunctional_regular _ _ _

theorem primePoleU_single (hp4 : 3 < p) (j : Fin 4) :
    primePoleU hp4 0 (Pi.single j 1) = primeUPole (by omega) j.val (by omega) :=
  restrictedPoleFunctional_single _ _ j

theorem primePoleV_single (hp4 : 3 < p) (j : Fin 4) :
    primePoleV hp4 0 (Pi.single j 1) = primeVPole (by omega) j.val (by omega) :=
  restrictedPoleFunctional_single _ _ j

theorem primePoleU_coeff_bound (hp4 : 3 < p)
    (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (hr : ∀ i, ‖r i‖ ≤ B) (n : ℕ) :
    ‖(primePoleU hp4 f r).coeff n‖ ≤ B :=
  restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

theorem primePoleV_coeff_bound (hp4 : 3 < p)
    (f : PowerSeries ℤ_[p]) (r : Fin 4 → ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B) (hr : ∀ i, ‖r i‖ ≤ B) (n : ℕ) :
    ‖(primePoleV hp4 f r).coeff n‖ ≤ B :=
  restrictedPoleFunctional_coeff_bound _ _ f r B hB hf hr n

theorem primePoleUV_well_defined (hp4 : 3 < p)
    (f g : PowerSeries ℤ_[p]) (hf : PowerSeries.IsRestricted 1 f)
    (hg : PowerSeries.IsRestricted 1 g) (r s : Fin 4 → ℤ_[p])
    (he : integralPoleNumerator (primePoleCenters p) f r =
      integralPoleNumerator (primePoleCenters p) g s) :
    primePoleU hp4 f r = primePoleU hp4 g s ∧
      primePoleV hp4 f r = primePoleV hp4 g s := by
  obtain ⟨rfl, rfl⟩ := integralPoleNumerator_injective _ primePoleCenters_injective f g hf hg r s he
  exact ⟨rfl, rfl⟩

end
end Li2

end
