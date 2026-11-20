import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximalCompactUnitaryArchimedean
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMaximalCompactUnitaryArchimedean.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.maximal_compact_unitary_archimedean : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ k ∈ K D n, ∀ τ, (mat k).map ((θ τ).comp (infPart D)) * ((mat k).map ((θ τ).comp (infPart D)))ᴴ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.MM.KUnitary.map_mul_conjTranspose_eq_one | exact GlobalTheory.CompanionTheory.MM.KUnitary.map_mul_conjTranspose_eq_one | (intros; apply GlobalTheory.CompanionTheory.MM.KUnitary.map_mul_conjTranspose_eq_one <;> assumption)
