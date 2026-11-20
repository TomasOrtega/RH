import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PmExactnessOfExP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPmExactnessOfExP.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.pm_exactness_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι), ExP P.M (fun h x => P.res h x) → P.Ex := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP <;> assumption)
