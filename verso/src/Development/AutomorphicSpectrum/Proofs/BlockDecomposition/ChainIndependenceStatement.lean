import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainIndependence
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FChainIndependence.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.chain_independence : ReciprocityTheory.Ty.Fin.St.ChainIndep := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.chainIndep | exact GlobalTheory.CompanionTheory.TyFin.chainIndep | (intros; apply GlobalTheory.CompanionTheory.TyFin.chainIndep <;> assumption)
