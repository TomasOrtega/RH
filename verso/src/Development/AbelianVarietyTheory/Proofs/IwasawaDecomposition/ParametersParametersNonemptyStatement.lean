import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSizeParametersNonempty.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.exists_sizeData_parameterChoice : (∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ L : SizeData₂ (w.D Z), Nonempty (ParameterChoice' (w.D Z) L)) ∧ AllSt fun _ _ _ _ _ _ x => (∃ L : SizeData₂ (Dof x), Nonempty (ParameterChoice' (Dof x) L)) ∧ ∀ Lc : LocAll (lay0 (Dof x)), ∃ L : SizeData₂ (withLoc Lc), Nonempty (ParameterChoice' (withLoc Lc) L) := by
  first | exact @GlobalTheory.HeightCounting.Up.SizePar.exists_params | exact GlobalTheory.HeightCounting.Up.SizePar.exists_params | (intros; apply GlobalTheory.HeightCounting.Up.SizePar.exists_params <;> assumption)
