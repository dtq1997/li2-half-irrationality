module
public import Li2Unified.Modular.Base.RestrictedEvaluation
public import Li2Unified.Modular.Base.RestrictedDifferential

set_option backward.privateInPublic true

@[expose] public section

/-! Exact differential identities for the nonmatching inverse factors.
They follow from the inverse identity, without assuming convergence of a
geometric series at a p-adic unit. -/
namespace Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma inverseOneSubSeries_unique (b : ℤ_[p]) (d : ℕ) (f : PowerSeries ℤ_[p])
    (hf : f*(1-PowerSeries.C b*PowerSeries.X)^d = 1) :
    f = inverseOneSubSeries b d := by
  calc
    f = f*(inverseOneSubSeries b d*(1-PowerSeries.C b*PowerSeries.X)^d) := by
      rw [inverseOneSubSeries_identity, mul_one]
    _ = inverseOneSubSeries b d*(f*(1-PowerSeries.C b*PowerSeries.X)^d) := by ring
    _ = inverseOneSubSeries b d := by rw [hf, mul_one]

theorem inverseOneSubSeries_add (b : ℤ_[p]) (d e : ℕ) :
    inverseOneSubSeries b (d+e) = inverseOneSubSeries b d*inverseOneSubSeries b e := by
  symm
  apply inverseOneSubSeries_unique
  rw [pow_add, mul_mul_mul_comm, inverseOneSubSeries_identity, inverseOneSubSeries_identity, mul_one]

lemma inverseOneSubSeries_square (b : ℤ_[p]) :
    (inverseOneSubSeries b 1)^2 = inverseOneSubSeries b 2 := by
  simpa only [pow_two] using (inverseOneSubSeries_add b 1 1).symm

theorem inverseOneSubSeries_derivative_one (b : ℤ_[p]) :
    PowerSeries.derivative (R := ℤ_[p]) (inverseOneSubSeries b 1) =
      PowerSeries.C b*inverseOneSubSeries b 2 := by
  have h := inverseOneSubSeries_identity b 1
  rw [pow_one] at h
  have hd := (PowerSeries.derivative (R := ℤ_[p])).leibniz_of_mul_eq_one h
  simp only [map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub,
    inverseOneSubSeries_square] at hd
  simpa only [neg_mul_neg, mul_comm] using hd

theorem restrictedV_inverse_one (μ : ℕ → ℤ_[p]) (b : ℤ_[p]) (hb : ‖b‖ < 1) :
    restrictedV μ (inverseOneSubSeries b 1) =
      b*restrictedMoment μ (inverseOneSubSeries b 2) := by
  rw [restrictedV_derivative μ _ (inverseOneSubSeries_isRestricted b hb 1),
    inverseOneSubSeries_derivative_one]
  rw [← PowerSeries.smul_eq_C_mul]
  exact restrictedMoment_smul μ _ (inverseOneSubSeries_isRestricted b hb 2) b

end
end Li2

end
