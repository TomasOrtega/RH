import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsValueAdelicProductFormula
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FAbsValueAdelicProductFormula.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.absValue_adelic_product_formula : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ x : (AE D)ˣ, absA D x = (∏ τ, ‖θ τ (infPart D x.1)‖₊ ^ 2) * ∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) := by
  first | exact @GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod | exact GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod | (intros; apply GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod <;> assumption)
