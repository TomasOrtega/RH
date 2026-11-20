import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadical
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SeeOntoCusp.mem_NI_iff_iota` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMemUnipotentRadicalIffIotaMemAdelicRadical.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  first | exact @GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | exact GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | (intros; apply GlobalTheory.SeeOntoCusp.mem_NI_iff_iota <;> assumption)
