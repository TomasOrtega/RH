import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Introduce `Y' Y T j s t hj`. Use `haveI := hj.op`. Set `U : T.Opens` to `s ⁻¹ᵁ j.opensRange ⊓ t ⁻¹ᵁ j.opensRange`. Establish `hs : Set.range (U.ι ≫ s) ⊆ Set.range j`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hx.1`. Establish `ht : Set.range (U.ι ≫ t) ⊆ Set.range j`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Conclude with `hx.2`. Use `⟨U, U.ι, IsOpenImmersion.lift j _ hs, IsOpenImmersion.lift j _ ht, ⟨inferInstance, ?_, IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩⟩` and prove the remaining obligations. Rewrite using `[Scheme.Opens.range_ι]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Int.Geo.Cut.resEx :
    UpperTheory.Gal.Int.Geo.Cut.ResEx := by
  intro Y' Y T j s t hj
  haveI := hj.op
  let U : T.Opens := s ⁻¹ᵁ j.opensRange ⊓ t ⁻¹ᵁ j.opensRange
  have hs : Set.range (U.ι ≫ s) ⊆ Set.range j := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have ht : Set.range (U.ι ≫ t) ⊆ Set.range j := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine ⟨U, U.ι, IsOpenImmersion.lift j _ hs, IsOpenImmersion.lift j _ ht,
    ⟨inferInstance, ?_, IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩⟩
  rw [Scheme.Opens.range_ι]
  rfl
