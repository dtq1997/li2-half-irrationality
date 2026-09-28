module
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

set_option backward.privateInPublic true

@[expose] public section
/-
SPDX-License-Identifier: Apache-2.0
Adapted from Apery/CircleAtoms.lean in mo271/Zeta5 by Moritz Firsching (https://github.com/mo271/Zeta5),
commit f19a1960609f7d38e7b63fd2acb05e6f60a7b741.
See licenses/LICENSE-Zeta5.txt for the upstream Apache 2.0 license.
Narrow imports and Li2 namespace; retain only the stated logarithmic
integral tools; replace old circle fibers by fixed Mathlib countable preimages.
-/

open MeasureTheory Real intervalIntegral
namespace Li2

lemma circle_log_integrable (c a : ℂ) (R : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap c R θ - a‖) volume 0 (2 * π) :=
  circleIntegrable_log_norm_sub_const R

end Li2

end
