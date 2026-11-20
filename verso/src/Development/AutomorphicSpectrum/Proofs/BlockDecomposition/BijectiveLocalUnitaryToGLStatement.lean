import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBijectiveLocalUnitaryToGL.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.bijective_local_unitary_to_GL : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), Function.Bijective (thU D n v τ) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_bijective | exact GlobalTheory.CompanionTheory.Jp.thU_bijective | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_bijective <;> assumption)
