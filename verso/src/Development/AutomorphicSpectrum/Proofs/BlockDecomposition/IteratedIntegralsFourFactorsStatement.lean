import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactors
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIteratedIntegralsFourFactors.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.iterated_integrals_four_factors : Fub4 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds <;> assumption)
