import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem lamOf_lat (HI : IdealLattice) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ := by
  have hd : D.host.d ≠ 0 := by
    intro h0
    have hs : D.host.sqd = 0 := by
      have h := D.host.sqd_sq
      rw [h0] at h
      simp at h
      exact h
    have hK : D.host.K = ⊥ := by
      show IntermediateField.adjoin ℚ {D.host.sqd} = ⊥
      rw [hs]
      exact IntermediateField.adjoin_simple_eq_bot_iff.mpr (zero_mem _)
    have h1 := (IntermediateField.finrank_eq_one_iff).mpr hK
    have h2 := Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw)
    omega
  have hreal : IsEmpty (D.host.K →+* ℝ) := by
    refine ⟨fun f => ?_⟩
    have hs : (⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩ : D.host.K) ^ 2 =
        -((D.host.d : ℕ) : D.host.K) := by
      apply Subtype.ext
      simpa using D.host.sqd_sq
    have h2 := congrArg f hs
    rw [map_pow, map_neg, map_natCast] at h2
    have h3 := sq_nonneg (f ⟨D.host.sqd, Formalism.HC.HostRaw.sqd_mem_K (H := D.host.toHostRaw)⟩)
    have h4 : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    linarith
  obtain ⟨⟨w₁, w₂, hw, heq⟩, -⟩ :=
    HI D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) (Formalism.HC.HostRaw.finrank_K (H := D.host.toHostRaw))
      hreal cc δ hc hδ
  exact ⟨w₁, w₂, hw, heq⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem delta_ne (HI : IdealLattice) (HD : DiscrNe) (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat HI D cc hc 1 one_ne_zero
  intro h0
  have h12 : δ ^ 12 = discr (lamOf D cc 1) := hδ
  rw [h0, hL] at h12
  exact HD w₁ w₂ hw (by simpa using h12.symm)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the hypotheses and the conclusion using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem transInv_of (HI : IdealLattice) (HD : DiscrNe) (HS : SigmaStarEx) (HT : TransInvLat) (D : D7) : StandardLatticesGL3.transInv D := by
  intro cc δ hC x ω m hm hx hω
  obtain ⟨⟨hc, -⟩, hd12⟩ := hC
  have hδ : δ ≠ 0 := delta_ne HI HD D cc hc δ hd12
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat HI D cc hc δ hδ
  rw [hL] at hx hω ⊢
  have hspec := Classical.epsilon_spec (HS w₁ w₂ hw)
  exact HT w₁ w₂ hw _ hspec.2.2.2 x ω m hm hx hω

end Formalism.MainNotions.Ext
