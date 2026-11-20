import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTensorPreimmersion
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSpecTensorPreimmersion.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.spec_tensor_preimmersion : ∀ {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) (T : Scheme.Pullback.Triplet f g), IsPreimmersion T.SpecTensorTo := by
  first | exact @GlobalTheory.isPreimmersion_SpecTensorTo | exact GlobalTheory.isPreimmersion_SpecTensorTo | (intros; apply GlobalTheory.isPreimmersion_SpecTensorTo <;> assumption)
