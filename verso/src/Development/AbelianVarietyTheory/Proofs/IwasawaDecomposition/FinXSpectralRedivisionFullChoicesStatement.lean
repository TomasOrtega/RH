import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.SRe.finX_reY` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFinXSpectralRedivisionFullChoices.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.finX_spectralRedivisionFullChoices : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  first | exact @GlobalTheory.Mem.SRe.finX_reY | exact GlobalTheory.Mem.SRe.finX_reY | (intros; apply GlobalTheory.Mem.SRe.finX_reY <;> assumption)
