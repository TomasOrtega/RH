import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter

open CategoryTheory Limits AlgebraicGeometry

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.blOff :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpOff := by
  intro R _ _ Z W _ _ π hπ
  have hdg : IsClosedImmersion (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    change IsClosedImmersion (pullback.diagonal (Over.hom Z))
    infer_instance
  have hft : LocallyOfFiniteType (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) := by
    change LocallyOfFiniteType (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  have hln : IsLocallyNoetherian (Over.left (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  have hsupp : ((Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support : Set _) =
      Set.range (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    rw [Scheme.Hom.support_ker]
    exact (IsClosedImmersion.base_closed (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).isClosed_range.closure_eq
  refine ⟨FunctorialResolution.Blowup.isProper_of_isBlowupAlongIdealSheaf hπ, ?_, ?_⟩
  · change IsClosedImmersion (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
    infer_instance
  · intro U hU
    have hUeq : U = (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support.compl := by
      apply SetLike.coe_injective
      rw [hU]
      simp [hsupp]
    subst hUeq
    refine ⟨FunctorialResolution.Blowup.blowupIsIsoOffCenter _ _ _ _ hπ, ?_⟩
    change _ = (Set.range (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))))ᶜ
    rw [Scheme.Pullback.range_fst]
    simp [hsupp]
