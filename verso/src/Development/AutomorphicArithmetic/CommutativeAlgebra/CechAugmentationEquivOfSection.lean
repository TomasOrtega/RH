import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ Y X f s hs F`. Apply `(GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1` to reduce the goal to its premises. Apply `GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R (yoneda.map f)` to reduce the goal to its premises. Introduce `U g`. Use `⟨g ≫ s, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(g ≫ s) ≫ f = g`. Rewrite using `[Category.assoc, hs, Category.comp_id]`.
-/
theorem UpperTheory.cechAugmentation_equiv_of_section :
    ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ F : Shv R, Eqv R (cechAug f) F := by
  intro R _ Y X f s hs F
  apply (GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1
  apply GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R (yoneda.map f)
  intro U g
  refine ⟨g ≫ s, ?_⟩
  change (g ≫ s) ≫ f = g
  rw [Category.assoc, hs, Category.comp_id]
