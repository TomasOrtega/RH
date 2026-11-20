import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoExtendScalarsTateTwistAugmentation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuasiIsoExtendScalarsTateTwistAugmentation.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.quasiIso_extendScalars_tateTwist_augmentation : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (i : ℤ), QuasiIso (extAug (ZMod.castHom hq (ZMod q)) (tw Q i)) := by
  first | exact @GlobalTheory.EtC.ExtQis.quasiIso_extAug | exact GlobalTheory.EtC.ExtQis.quasiIso_extAug | (intros; apply GlobalTheory.EtC.ExtQis.quasiIso_extAug <;> assumption)
