import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothForms.denomBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FUnitaryLatticeDenominatorHeightBoundProof.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), DenomBound θ V := by
  first | exact @GlobalTheory.SmoothForms.denomBound | exact GlobalTheory.SmoothForms.denomBound | (intros; apply GlobalTheory.SmoothForms.denomBound <;> assumption)
