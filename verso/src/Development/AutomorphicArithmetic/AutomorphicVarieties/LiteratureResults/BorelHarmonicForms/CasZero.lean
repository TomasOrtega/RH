import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DelCochain
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Lit.Bor.casZero :
    UpperTheory.V.Lit.Bor.CasZero := by
  intro E _ _ _ a n e he M _ _ _ _ κ A B hA hB hAB hκ hinf c hc hcoh
  by_contra hne
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (B - A) e (0 : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) X = 0 := fun q X => by
    rw [del_apply]
    simp
  rcases hcoh with ⟨ω, hco, hcl, hnz⟩ | ⟨q, ω, hco, hcl, hne'⟩
  · apply hnz
    ext X
    have h := kugaZero E a n e M A B hAB ω (hinf 0 ω hco) X
    rw [hcl, hdel, hc] at h
    exact (smul_eq_zero.1 h.symm).resolve_left hne
  · have hδ := delCochain E a n e he M κ (B - A) hκ q ω hco
    let s : M →ₗ[ℝ] M := (c⁻¹ • LinearMap.id : M →ₗ[ℂ] M).restrictScalars ℝ
    have hs : ∀ X, s.compAlternatingMap (del (B - A) e ω) X = c⁻¹ • del (B - A) e ω X := fun X => rfl
    refine hne' (s.compAlternatingMap (del (B - A) e ω)) (fun k X => ?_) (AlternatingMap.ext fun X => ?_)
    · rw [hs, hs, map_smul, hδ k X]
    · have h := kugaSucc E a n e he M A B hA hB hAB q ω (hinf _ ω hco) X
      rw [hcl, hdel, add_zero, hc, dCo_apply] at h
      have h2 : ω X = c⁻¹ • (c • ω X) := (inv_smul_smul₀ hne _).symm
      rw [dCo_apply, h2, ← h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hs, map_smul, smul_comm c⁻¹]
