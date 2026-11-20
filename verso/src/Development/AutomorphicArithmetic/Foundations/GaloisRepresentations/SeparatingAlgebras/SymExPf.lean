import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
import GroundTheory.AutomorphicForms.Satake

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Gen.symEx_pf :
    UpperTheory.Gal.Gen.SymEx := by
  intro n Φ
  refine ⟨polyEmb n (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩
  · show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _
    intro τ
    rw [← polyEmb_rename]
    congr 1
    rw [map_prod]
    simp_rw [MvPolynomial.rename_rename]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  · intro z
    rw [evalAt_polyEmb, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [MvPolynomial.aeval_rename]
    rfl
  · intro hΦ
    refine ⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro σ _ h
      apply hΦ
      exact MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])
    · rw [evalAt_polyEmb]
      rfl
