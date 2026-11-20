import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelLocalOfToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FSiegelLocalOfToroidalIntegral.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.siegel_local_of_toroidal_integral : GlobalTheory.Published.SiegelToroidalIntegral → SiegLocSt := by
  first | exact @GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral | exact GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral | (intros; apply GlobalTheory.SiegLoc.siegLocSt_of_siegelToroidalIntegral <;> assumption)
