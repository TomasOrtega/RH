import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `X s`. Set `Ω : Type` to `AlgebraicClosure (X.residueField s)`. Set `y : gp Ω ⟶ Spec (X.residueField s)` to `Spec.map (CommRingCat.ofHom (algebraMap (X.residueField s) Ω))`. Use `⟨Ω, inferInstance, inferInstance, y ≫ X.fromSpecResidueField s, ?_⟩` and prove the remaining obligations. Rewrite using `[pt_comp]`.

Conclude with `Scheme.fromSpecResidueField_apply s (pt y)`.
-/
theorem UpperTheory.Gal.TranscendenceTraces.ptEx_of :
    PtEx := by
  intro X s
  let Ω : Type := AlgebraicClosure (X.residueField s)
  let y : gp Ω ⟶ Spec (X.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField s) Ω))
  refine ⟨Ω, inferInstance, inferInstance, y ≫ X.fromSpecResidueField s, ?_⟩
  rw [pt_comp]
  exact Scheme.fromSpecResidueField_apply s (pt y)
