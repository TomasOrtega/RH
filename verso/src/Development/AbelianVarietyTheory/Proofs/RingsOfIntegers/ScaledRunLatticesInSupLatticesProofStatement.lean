import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProof
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FRingsOfIntegers%2FScaledRunLatticesInSupLatticesProof.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.scaledRunLattices_in_supLattices : ScaledLatticesInSupLattices := by
  first | exact @GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | exact GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | (intros; apply GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof <;> assumption)
