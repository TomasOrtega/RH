import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzRestrictionColumns
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ColSlice.integrable_slice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegrableSchwartzRestrictionColumns.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.integrable_schwartz_restriction_columns : ∀ {D : D7} {n r t : ℕ} {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n) (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure] (Φ : schwartzA θ a n) (x : Mx D a r), Integrable (fun v => Φ.1 (jn hn x v)) μt := by
  first | exact @GlobalTheory.CompanionTheory.ColSlice.integrable_slice | exact GlobalTheory.CompanionTheory.ColSlice.integrable_slice | (intros; apply GlobalTheory.CompanionTheory.ColSlice.integrable_slice <;> assumption)
