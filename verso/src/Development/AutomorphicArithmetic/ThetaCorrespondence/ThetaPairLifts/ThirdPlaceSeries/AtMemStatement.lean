import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrameStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMem
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FAtMem.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.g0_lift_unitary_central_frame_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ _ =>
  ∀ s, ∃ L : G0g (w.st Z).toD7.nd → Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
    GlobalTheory.PendOf.IsTypeGroupBlockLift (w.st Z).toD7 (w.st Z).toD7.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV) ∧
    ∀ g (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ t.r.z.R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ t.r.z.R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (t.r.z.R.eG ((t.r.z.R.eG.trans t.r.z.cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  first | exact @_root_.GlobalTheory.BlockLiftFrame.atMem_alt | exact _root_.GlobalTheory.BlockLiftFrame.atMem_alt | (intros; apply _root_.GlobalTheory.BlockLiftFrame.atMem_alt <;> assumption)
end
