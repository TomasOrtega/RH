import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXi
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HatNF.topDensity_cut_dominated_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FTopDensityCutoffDominatedOfHCXi.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.topDensity_cutoff_dominated_of_HC_xi : GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  first | exact @GlobalTheory.HatNF.topDensity_cut_dominated_all | exact GlobalTheory.HatNF.topDensity_cut_dominated_all | (intros; apply GlobalTheory.HatNF.topDensity_cut_dominated_all <;> assumption)
