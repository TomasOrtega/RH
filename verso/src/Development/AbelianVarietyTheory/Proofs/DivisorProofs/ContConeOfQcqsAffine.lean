import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousOnConeOfWhiskerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeQcqsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ F hF I _ _ G c hc hcp hqs haff`. Take `⟨i₀⟩ : Nonempty I` from `IsCofiltered.nonempty`. Establish `hc' : IsLimit ((Over.conePost G i₀).obj c)` using `Over.isLimitConePost i₀ hc`. Use `haveI := hcp i₀`. Use `haveI := hqs i₀`.

Establish `hcore` using `GlobalTheory.T.cohomologyContinuous_baseChange_qcqs R F hF (G.obj i₀) (Over i₀) (Over.post G) ((Over.conePost G i₀).obj c) hc' (fun j => haff _ _ j.hom) (G.obj i₀) (𝟙 _)`. Establish `hb` using `GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F`. Use `haveI : IsIso (sch.map (𝟙 (G.obj i₀))) := inferInstance`. Apply `GlobalTheory.T.cohomologyContinuousOnCone_of_whisker R F I (Over i₀) (Over.forget i₀) (G ⋙ sch) (sch.mapCone c)` to reduce the goal to its premises. Introduce `i`.

Conclude with `⟨Over.mk (IsCofiltered.minToRight i i₀), ⟨IsCofiltered.minToLeft i i₀⟩⟩`. Set `α : Over.post G ⋙ bc (sch.map (𝟙 (G.obj i₀))) ⟶ Over.forget i₀ ⋙ G ⋙ sch` to `{ app := fun j => pullback.snd _ _ naturality := fun j k f => by`. Simplify using `only [Functor.comp_map, bc, pullback.map]`. Use `erw [pullback.lift_snd]`. Use `rfl }`.

Use `(GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F (Over i₀) _ _ ((bc (sch.map (𝟙 (G.obj i₀)))).mapCone ((Over.conePost G i₀).obj c)) ((sch.mapCone c).whisker (Over.forget i₀)) α (pullback.snd _ _) ?_ ?_ ?_).1 hcore` and prove the remaining obligations. Introduce `j`. Simplify using `only [Functor.mapCone_π_app, Cone.whisker_π, bc, pullback.map]`. Use `erw [pullback.lift_snd]`. Both sides reduce to the same expression.

Introduce `j`. Conclude with `hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)`. Conclude with `hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)`.
-/
theorem contCone_of_qcqs_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  intro R _ F hF I _ _ G c hc hcp hqs haff
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have hc' : IsLimit ((Over.conePost G i₀).obj c) := Over.isLimitConePost i₀ hc
  haveI := hcp i₀
  haveI := hqs i₀
  have hcore := GlobalTheory.T.cohomologyContinuous_baseChange_qcqs R F hF (G.obj i₀) (Over i₀) (Over.post G) ((Over.conePost G i₀).obj c) hc'
    (fun j => haff _ _ j.hom) (G.obj i₀) (𝟙 _)
  have hb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  haveI : IsIso (sch.map (𝟙 (G.obj i₀))) := inferInstance
  apply GlobalTheory.T.cohomologyContinuousOnCone_of_whisker R F I (Over i₀) (Over.forget i₀) (G ⋙ sch) (sch.mapCone c)
  · intro i
    exact ⟨Over.mk (IsCofiltered.minToRight i i₀), ⟨IsCofiltered.minToLeft i i₀⟩⟩
  · let α : Over.post G ⋙ bc (sch.map (𝟙 (G.obj i₀))) ⟶ Over.forget i₀ ⋙ G ⋙ sch :=
      { app := fun j => pullback.snd _ _
        naturality := fun j k f => by
          simp only [Functor.comp_map, bc, pullback.map]
          erw [pullback.lift_snd]
          rfl }
    refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F (Over i₀) _ _ ((bc (sch.map (𝟙 (G.obj i₀)))).mapCone ((Over.conePost G i₀).obj c))
      ((sch.mapCone c).whisker (Over.forget i₀)) α (pullback.snd _ _) ?_ ?_ ?_).1 hcore
    · intro j
      simp only [Functor.mapCone_π_app, Cone.whisker_π, bc, pullback.map]
      erw [pullback.lift_snd]
      rfl
    · intro j
      exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
    · exact hb.1 _ _ _ (pullback_snd_iso_of_left_iso _ _)
end GlobalTheory.EtC
