import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `hBC hFlat hUniq hMBC Z' S' Z S v p' p g _ _ _ pb hN hD`. Use `haveI : IsFinite p' := MorphismProperty.of_isPullback pb ‹_›`. Use `hUniq p' _ _ (hBC v p' p g _ pb hN.1) (hFlat p') _ hD ?_` and prove the remaining obligations. Introduce `Ω _ _ z hz`. Rewrite using `[hMBC v p' p g pb]`.

Use `hN.2 Ω (z ≫ v) ?_` and prove the remaining obligations. Establish `e : (z ≫ v) ≫ p = (z ≫ p') ≫ g`. Rewrite using `[Category.assoc, pb.w, Category.assoc]`. Rewrite using `[e, pt_comp]`. Conclude with `hz`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.nwtFlat_of :
    WtBC → WtFlat → WtUnique → MultBC → NwtFlat := by
  intro hBC hFlat hUniq hMBC Z' S' Z S v p' p g _ _ _ pb hN hD
  haveI : IsFinite p' := MorphismProperty.of_isPullback pb ‹_›
  refine hUniq p' _ _ (hBC v p' p g _ pb hN.1) (hFlat p') _ hD ?_
  intro Ω _ _ z hz
  rw [hMBC v p' p g pb]
  refine hN.2 Ω (z ≫ v) ?_
  have e : (z ≫ v) ≫ p = (z ≫ p') ≫ g := by
    rw [Category.assoc, pb.w, Category.assoc]
  rw [e, pt_comp]
  exact hz
