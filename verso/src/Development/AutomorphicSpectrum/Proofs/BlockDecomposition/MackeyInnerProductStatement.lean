import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProduct
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMackeyInnerProduct.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.mackey_inner_product : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  first | exact @GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | exact GlobalTheory.CompanionTheory.MackeyFn.mackeyIp | (intros; apply GlobalTheory.CompanionTheory.MackeyFn.mackeyIp <;> assumption)
