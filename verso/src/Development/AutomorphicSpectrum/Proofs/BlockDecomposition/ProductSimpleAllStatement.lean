import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSimpleAll
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductSimpleAll.lean&line=170#L170)
-/
theorem _root_.GlobalTheory.T.product_simple_all : ReciprocityTheory.Ty.Fin.St.ProdSimpleAll := by
  first | exact @GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll | exact GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll | (intros; apply GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll <;> assumption)
