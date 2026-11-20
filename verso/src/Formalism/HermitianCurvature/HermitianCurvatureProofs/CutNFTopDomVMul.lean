import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomPtw

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem vector_multiplication_holds : NFVMul := by
  intro Wp Wq _ _ _ _ _ _ P p φ F γ _hγ hG
  by_cases hc : ((φ (TBB.Gp p γ) : ℝ) : ℂ) = 0
  · rw [hc, zero_smul]
    unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · have hae : ∀ᵐ q ∂p.T.base.μSS,
          D.orbIntegrand p.T.base h2.choose
            (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g) q =
          (1 : ℂ) • D.orbIntegrand p.T.base h2.choose (fun _ => (0 : Wq →L[ℂ] Wp)) q := by
        filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
        have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
          rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
          rfl
        unfold D.orbIntegrand B.rho
        simp [hGq, hc]
      rw [TBBx4.orbJ_smul_ae _ _ _ _ _ _ one_ne_zero hae, one_smul]
      have h0 := TBBx4.orbJ_smul_ae p.T.base h2.choose
        (D.muR p.T.base h2.choose (h1.1.2 ▸ D.ptPerm γ)) (fun _ => (0 : Wq →L[ℂ] Wp))
        (fun _ => (0 : Wq →L[ℂ] Wp)) (2 : ℂ) two_ne_zero
        (ae_of_all _ fun q => by unfold D.orbIntegrand B.rho; simp)
      rw [two_smul] at h0
      simpa using h0
    · simp
    · simp
  · unfold KB.Pl.V D.vecV
    split_ifs with h1 h2
    · apply TBBx4.orbJ_smul_ae _ _ _ _ _ _ hc
      filter_upwards [TBBx2.ae_inSS p.T.base] with q hq
      have hGq : Gf P.k P.r p.T.base.z p.T.base.z' (B.sgs q h2.choose) = TBB.Gp p γ := by
        rw [TBBx2.Gf_sgs _ q hq, TBBx2.Gf_of_Zhat _ _ _ _ h2.choose_spec.2.1]
        rfl
      unfold D.orbIntegrand B.rho
      simp only [hGq, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [smul_comm]
    · simp
    · simp

end

end Formalism.FourierDecayAlt.P.CutBP
