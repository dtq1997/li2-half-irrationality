module
public import Li2Unified.Modular.Base.FieldPoleCompatibility
public import Li2Unified.Modular.Base.FieldParameterFunctional
public import Li2Unified.Modular.Base.PrimeFourPolePullback
public import Li2Unified.Modular.Base.PrimeDiscShapes
public import Li2Unified.Modular.Base.DissectedSquareRecurrence
public import Li2Unified.Modular.Base.DissectedSquare
public import Li2Unified.Modular.Base.PoleWindowReversal
public import Mathlib.Data.Fin.Rev
public import Li2Unified.Modular.Base.PulledPoleValues
public import Li2Unified.Modular.Base.ParameterDifferentialDissection

set_option backward.privateInPublic true

@[expose] public section

/-! Independent local presentation from the ORIGINAL quotient and residues.
Matching original poles give one of the four integral centers; nonmatching
poles give the previously constructed reciprocal series. No target local shape
or equality of functionals is used to define this presentation. -/
open Polynomial
open scoped BigOperators
namespace Li2
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

def originalResidue (m : ℕ) (F : ℚ[X]) (j : ℕ) : ℚ :=
  F.eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 m).erase j, ((l:ℚ)-(j:ℚ))

def pulledPoleRegular (j a : ℕ) : PowerSeries ℚ_[p] :=
  if hm : p ∣ j+(p-1-a)+1 then 0
  else PowerSeries.map (algebraMap ℤ_[p] ℚ_[p])
    (padicReciprocalSeries (((j+(p-1-a)+1:ℕ):ℚ)-(p:ℚ))
      (rational_nonmultiple_sub_prime _ hm).1 (rational_nonmultiple_sub_prime _ hm).2 1)

def pulledPoleResidue (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p) : Fin 4 → ℚ_[p] :=
  if hm : p ∣ j+(p-1-a)+1 then
    Pi.single (primeMatchingPoleIndex j a hj ha hm) (p:ℚ_[p])⁻¹
  else 0

theorem pulledPoleRegular_isRestricted (j a : ℕ) :
    PowerSeries.IsRestricted 1 (pulledPoleRegular (p := p) j a) := by
  unfold pulledPoleRegular
  split_ifs with hm
  · exact PowerSeries.isRestricted_zero 1
  · exact field_map_isRestricted _ (padicReciprocalSeries_isRestricted _ _ _ _)

lemma primeMatchingPole_denominator (j a : ℕ) (hj : j ≤ 4*p-4) (ha : a < p)
    (hm : p ∣ j+(p-1-a)+1) :
    (j:ℚ_[p])-(a:ℚ_[p]) = (p:ℚ_[p])*(primeMatchingPoleIndex j a hj ha hm).val := by
  have hq : 0 < (j+(p-1-a)+1)/p :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hm) hp.out.pos
  have he : j = p*((j+(p-1-a)+1)/p-1)+a := by
    have ht := Nat.mul_div_cancel' hm
    rw [show (j+(p-1-a)+1)/p = ((j+(p-1-a)+1)/p-1)+1 by omega,
      Nat.mul_add, Nat.mul_one] at ht
    have hi := polePullback_index j a ha
    omega
  have hc : (j:ℚ_[p]) = (p:ℚ_[p])*(((j+(p-1-a)+1)/p-1:ℕ):ℚ_[p])+(a:ℚ_[p]) := by
    exact_mod_cast he
  change (j:ℚ_[p])-(a:ℚ_[p]) = (p:ℚ_[p])*(((j+(p-1-a)+1)/p-1:ℕ):ℚ_[p])
  rw [hc, add_sub_cancel_right]

def originalPulledRegular (m : ℕ) (F : ℚ[X]) (a : Fin p) : PowerSeries ℚ_[p] :=
  rationalPolynomialSeries ((F /ₘ D m).comp (C (p:ℚ)*X-C (a.val:ℚ))) +
    ∑ j ∈ Finset.Icc 1 m, PowerSeries.C (originalResidue m F j : ℚ_[p])*pulledPoleRegular j a.val

def originalPulledResidue (m : ℕ) (hm : m ≤ 4*p-4) (F : ℚ[X]) (a : Fin p) : Fin 4 → ℚ_[p] :=
  fun i => ∑ j : ↥(Finset.Icc 1 m), (originalResidue m F j.val : ℚ_[p])*
    pulledPoleResidue j.val a.val ((Finset.mem_Icc.mp j.property).2.trans hm) a.isLt i

lemma field_restricted_finset_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ_[p])
    (hf : ∀ i ∈ s, PowerSeries.IsRestricted 1 (f i)) :
    PowerSeries.IsRestricted 1 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact PowerSeries.isRestricted_zero 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PowerSeries.isRestricted.add 1 (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem originalPulledRegular_isRestricted (m : ℕ) (F : ℚ[X]) (a : Fin p) :
    PowerSeries.IsRestricted 1 (originalPulledRegular m F a) := by
  apply PowerSeries.isRestricted.add 1
  · exact field_polynomial_isRestricted _
  · apply field_restricted_finset_sum
    intro j _
    exact PowerSeries.isRestricted.mul 1 (PowerSeries.isRestricted_C 1 _)
      (pulledPoleRegular_isRestricted j a.val)

end
end Li2

end
