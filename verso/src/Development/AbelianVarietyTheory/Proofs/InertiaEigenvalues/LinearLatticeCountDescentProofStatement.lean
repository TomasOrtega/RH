import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.Desc.linearDescent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLinearLatticeCountDescentProof.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.linearLatticeCountDescent_proof : LinearDescent := by
  first | exact @GlobalTheory.UnitLemma.Desc.linearDescent | exact GlobalTheory.UnitLemma.Desc.linearDescent | (intros; apply GlobalTheory.UnitLemma.Desc.linearDescent <;> assumption)
