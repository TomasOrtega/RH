import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffSplitOfEqOffSplitPrime
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FEqOffSplitOfEqOffSplitPrime.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.eqOffSplit_of_eqOff_splitPrime : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := by
  first | exact @GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff | exact GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff | (intros; apply GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff <;> assumption)
