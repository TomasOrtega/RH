import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNonemptyCompactDualHaar.lean&line=235#L235)
-/
theorem _root_.GlobalTheory.T.nonempty_compactDualHaar : Nonempty CDHaar := by
  first | exact @GlobalTheory.CompactDualExists.nonempty_cdHaar | exact GlobalTheory.CompactDualExists.nonempty_cdHaar | (intros; apply GlobalTheory.CompactDualExists.nonempty_cdHaar <;> assumption)
