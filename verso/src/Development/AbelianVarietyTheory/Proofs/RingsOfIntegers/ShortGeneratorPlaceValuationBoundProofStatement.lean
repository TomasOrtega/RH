import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShortBound.shortBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FRingsOfIntegers%2FShortGeneratorPlaceValuationBoundProof.lean&line=236#L236)
-/
theorem _root_.GlobalTheory.T.shortGeneratorPlaceValuationBound_proof : ShortBoundSt := by
  first | exact @GlobalTheory.ShortBound.shortBound | exact GlobalTheory.ShortBound.shortBound | (intros; apply GlobalTheory.ShortBound.shortBound <;> assumption)
