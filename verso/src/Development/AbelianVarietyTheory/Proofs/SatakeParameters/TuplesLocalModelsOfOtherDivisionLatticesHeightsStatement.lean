import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeights
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Svd.modelsAt_tr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTuplesLocalModelsOfOtherDivisionLatticesHeights.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  first | exact @GlobalTheory.Svd.modelsAt_tr | exact GlobalTheory.Svd.modelsAt_tr | (intros; apply GlobalTheory.Svd.modelsAt_tr <;> assumption)
