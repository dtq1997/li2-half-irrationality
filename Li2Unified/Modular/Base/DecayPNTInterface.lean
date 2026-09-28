module
public import Li2Unified.Modular.Base.DecayPNTConsequences

set_option backward.privateInPublic true

@[expose] public section

/-! the prime number theorem in Chebyshev form, stated with the fully
qualified Mathlib function (no local notation), so the ported proof cannot have replaced θ. -/
theorem Li2.theta_isEquivalent_id : Asymptotics.IsEquivalent Filter.atTop Chebyshev.theta id :=
  Li2.PNT.chebyshev_asymptotic

#print axioms Li2.theta_isEquivalent_id

end
