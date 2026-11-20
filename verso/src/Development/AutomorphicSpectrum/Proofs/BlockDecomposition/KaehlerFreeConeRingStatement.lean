import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKaehlerFreeConeRing.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.kaehler_free_cone_ring : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)), Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om <;> assumption)
