import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.InertialTypesAlt.unifTower :
    LiftsFix → PlaceEx → UnrOfIne → UnifTower := by
  intro hF hP hU E Ω _ _ _ n X Y hXY
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro A _ v w hv hw g hg
    have hvw : v = w := by
      apply HeightOneSpectrum.ext
      ext x
      rw [← hv x, hw x]
    rw [← hvw]
    exact hg
  | @head X Z hs hZY ih =>
    intro A hI v w hv hw g hg
    obtain ⟨_, _, _, _, _⟩ := hs
    obtain ⟨u, hu, -⟩ := hP X.K Z.K Ω A v hv n Z.π
    have hfix : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht z
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY z
      have := hI t ht y
      rwa [hy] at this
    have hgu : ((g : ℕ) : 𝓞 Z.K) ∉ u.asIdeal ^ 2 := by
      have h3 := (hU X.K Z.K Ω A v u hv hu hfix).2.2 (g : 𝓞 X.K) hg
      rwa [map_natCast] at h3
    refine ih A (fun t ht => ?_) u w hu hw g hgu
    exact hI (AlgEquiv.restrictScalars X.K t) ht
