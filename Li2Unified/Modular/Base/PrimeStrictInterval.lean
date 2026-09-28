module
public import Li2Unified.Modular.Base.PrimeEndpointTerms

set_option backward.privateInPublic true

@[expose] public section

open Finset Filter Topology Real
namespace Li2.PrimeSums
noncomputable section

lemma sum_Ioc_floor_eq_strict_add_endpoint {u v : ℝ} (hu : 0 ≤ u) (huv : u < v)
    (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, f k) =
      (∑ k ∈ (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun k : ℕ => (k : ℝ) < v), f k)+
      (if (⌊v⌋₊ : ℝ) = v then f ⌊v⌋₊ else 0) := by
  by_cases he : (⌊v⌋₊ : ℝ) = v
  · have hlast : ⌊v⌋₊ ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ := by
      apply Finset.mem_Ioc.mpr
      refine ⟨(Nat.floor_lt hu).mpr ?_, le_rfl⟩
      simpa only [he] using huv
    have hfilter : (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun k : ℕ => (k : ℝ) < v) =
        (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).erase ⌊v⌋₊ := by
      ext k
      have hcast : (k : ℝ) < v ↔ k < ⌊v⌋₊ := by
        simpa only [he] using (Nat.cast_lt (α := ℝ) (m := k) (n := ⌊v⌋₊))
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_Ioc, hcast]
      omega
    rw [hfilter, if_pos he]
    exact (Finset.sum_erase_add _ _ hlast).symm
  · have hv : 0 ≤ v := hu.trans huv.le
    have htop : (⌊v⌋₊ : ℝ) < v := by
      rcases lt_or_eq_of_le (Nat.floor_le hv) with hlt | heq
      · exact hlt
      · exact (he heq).elim
    have hfilter : (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun k : ℕ => (k : ℝ) < v) =
        Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ := by
      apply Finset.filter_eq_self.mpr
      intro k hk
      have hk' : (k : ℝ) ≤ (⌊v⌋₊ : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp hk).2
      exact hk'.trans_lt htop
    rw [hfilter, if_neg he, add_zero]

def affineOpenSum (α β a b x : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Ioc ⌊a*x⌋₊ ⌊b*x⌋₊).filter (fun k : ℕ => (k : ℝ) < b*x),
    (α*(k : ℝ)+β*x)*cPrime k

lemma mem_affineOpenSupport {a b x : ℝ} {k : ℕ}
    (ha : 0 ≤ a*x) (hb : 0 ≤ b*x) :
    k ∈ (Finset.Ioc ⌊a*x⌋₊ ⌊b*x⌋₊).filter (fun k : ℕ => (k : ℝ) < b*x) ↔
      a*x < (k : ℝ) ∧ (k : ℝ) < b*x := by
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · intro h
    exact ⟨(Nat.floor_lt ha).mp h.1.1, h.2⟩
  · intro h
    exact ⟨⟨(Nat.floor_lt ha).mpr h.1, (Nat.le_floor_iff hb).mpr h.2.le⟩, h.2⟩

lemma affineSum_eq_open_add_endpoint (α β : ℝ) {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hx : 0 < x) :
    affineSum α β a b x = affineOpenSum α β a b x+endpointTerm α β b x := by
  simpa only [affineSum, affineOpenSum, endpointTerm] using
    sum_Ioc_floor_eq_strict_add_endpoint (mul_nonneg ha hx.le)
      (mul_lt_mul_of_pos_right hab hx) (fun k => (α*(k : ℝ)+β*x)*cPrime k)

theorem affineOpenSum_tendsto (α β : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun x : ℝ => affineOpenSum α β a b x/x^2) atTop
      (𝓝 (α*((b^2-a^2)/2)+β*(b-a))) := by
  have h := (affineSum_tendsto α β ha hab.le).sub
    (endpointTerm_tendsto_zero α β (ha.trans hab))
  have he : (fun x : ℝ => affineSum α β a b x/x^2-endpointTerm α β b x/x^2) =ᶠ[atTop]
      (fun x : ℝ => affineOpenSum α β a b x/x^2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [affineSum_eq_open_add_endpoint α β ha.le hab hx]
    ring
  simpa only [sub_zero] using (tendsto_congr' he).mp h

theorem affineOpenSum_nat_tendsto (α β : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n : ℕ => affineOpenSum α β a b (n : ℝ)/(n : ℝ)^2) atTop
      (𝓝 (α*((b^2-a^2)/2)+β*(b-a))) :=
  (affineOpenSum_tendsto α β ha hab).comp tendsto_natCast_atTop_atTop

end
end Li2.PrimeSums

end
