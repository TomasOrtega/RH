import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `hF hP hU E Ω _ _ _ n X Y hXY`. Proceed by induction on `hXY using Relation.ReflTransGen.head_induction_on with`. Consider the case `refl`. Introduce `A _ v w hv hw g hg`. Establish `hvw : v = w`.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[← hv x, hw x]`. Rewrite using `[← hvw]`. Conclude with `hg`.

Consider the case `@head X Z hs hZY ih`. Introduce `A hI v w hv hw g hg`. Take `⟨_, _, _, _, _⟩` from `hs`. Take `⟨u, hu, -⟩` from `hP X.K Z.K Ω A v hv n Z.π`. Establish `hfix : ∀ t ∈ Ine (F` using `X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by`.

Introduce `t ht z`. Take `⟨y, hy⟩` from `hF E Ω n Z Y hZY z`. Use `hI t ht y` as an intermediate fact. Rewrite `this` using `[hy]`. Then use the resulting hypothesis. Establish `hgu : ((g : ℕ) : 𝓞 Z.K) ∉ u.asIdeal ^ 2`.

Establish `h3` using `(hU X.K Z.K Ω A v u hv hu hfix).2.2 (g : 𝓞 X.K) hg`. Rewrite `h3` using `[map_natCast]`. Then use the resulting hypothesis. Use `ih A (fun t ht => ?_) u w hu hw g hgu` and prove the remaining obligations. Conclude with `hI (AlgEquiv.restrictScalars X.K t) ht`.
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
