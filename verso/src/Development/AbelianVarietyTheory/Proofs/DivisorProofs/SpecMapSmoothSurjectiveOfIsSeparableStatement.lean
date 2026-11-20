import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpecMapSmoothSurjectiveOfIsSeparable.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  first | exact @GlobalTheory.spec_map_smooth_surjective_of_isSeparable | exact GlobalTheory.spec_map_smooth_surjective_of_isSeparable | (intros; apply GlobalTheory.spec_map_smooth_surjective_of_isSeparable <;> assumption)
