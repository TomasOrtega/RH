import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FIsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz.lean&line=205#L205)
-/
theorem _root_.GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ), ∀ φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ := by
  first | exact @GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA | exact GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA | (intros; apply GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA <;> assumption)
