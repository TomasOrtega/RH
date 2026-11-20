import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationExistsOfComponents
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorRef.polExSt_of_steps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FPolarizationExistsOfComponents.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.polarization_exists_of_components : PolSuppSt → SiegLocSt → PolGlueSt → PhiDivZSt → PhiDivOSt → UniformSt → RefineSt → GenFanSt → GenMapSt → BlowExSt → BlowOrdSt → BlowPolSt → ConeArcSt → DomSt → PolExSt := by
  first | exact @GlobalTheory.TorRef.polExSt_of_steps | exact GlobalTheory.TorRef.polExSt_of_steps | (intros; apply GlobalTheory.TorRef.polExSt_of_steps <;> assumption)
