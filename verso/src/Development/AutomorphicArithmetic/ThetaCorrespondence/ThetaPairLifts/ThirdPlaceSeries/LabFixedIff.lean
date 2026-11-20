import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.CoefDuty.OPinModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.Mem.Col2
/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem labFixed_iff_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp) : LabFixed D ↔ LabFixed a.nt.D := by
  have e : ∀ D', D' = withLoc a.nt.L → (LabFixed D' ↔ LabFixed a.nt.D) := by
    rintro _ rfl
    exact labFixed_withLoc _
  exact e D a.nt.eq
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem labDat_gen_tame_at_plGw {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf nch tp} (h : _root_.GlobalTheory.CoefDuty.OPinAlt a) (k : Fin 2) (v : a.nt.D.nd.PlG k) :
    @Formalism.L2.NT.TameCoupled _ _ _ _ _ (a.nt.D.nd.plOm.1 (a.nt.D.naut.plGw k v)) _ ⟨a.nt.D.host.g_prime k⟩ (a.nt.A.grp.kv k v)
      (a.nt.D.ntypes.tg k v) (@GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
        (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)) := by
  rw [← h.gen k]
  exact a.nt.A.grp.tg_tame k v
end GlobalTheory.CoefDuty.OPinModel
end
end
