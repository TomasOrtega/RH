import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter

open CategoryTheory Limits AlgebraicGeometry

/- English proof (translation)
Introduce `R _ _ Z W _ _ π hπ`. Establish `hdg : IsClosedImmersion (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))`. Express the relevant statement in the definitionally equal form `IsClosedImmersion (pullback.diagonal (Over.hom Z))`. Use `infer_instance`. Establish `hft : LocallyOfFiniteType (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))`.

Express the relevant statement in the definitionally equal form `LocallyOfFiniteType (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)`. Use `infer_instance`. Establish `hln : IsLocallyNoetherian (Over.left (UpperTheory.Gal.KunnethLefschetz.G.XX Z))` using `LocallyOfFiniteType.isLocallyNoetherian (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))`. Establish `hsupp : ((Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support : Set _) = Set.range (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))`. Rewrite using `[Scheme.Hom.support_ker]`.

Conclude with `(IsClosedImmersion.base_closed (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).isClosed_range.closure_eq`. Use `⟨FunctorialResolution.Blowup.isProper_of_isBlowupAlongIdealSheaf hπ, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsClosedImmersion (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))) infer_instance`. Introduce `U hU`. Establish `hUeq : U = (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support.compl`.

Apply `SetLike.coe_injective` to reduce the goal to its premises. Rewrite using `[hU]`. Simplify using `[hsupp]`. Substitute `hUeq` using the available equality. Use `⟨FunctorialResolution.Blowup.blowupIsIsoOffCenter _ _ _ _ hπ, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = (Set.range (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))))ᶜ`. Rewrite using `[Scheme.Pullback.range_fst]`. Simplify using `[hsupp]`.
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
