import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ColClass.classes_and_weight` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FTransportRepresentsClassesWeightOne.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.transport_represents_classes_weight_one : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  first | exact @GlobalTheory.ColClass.classes_and_weight | exact GlobalTheory.ColClass.classes_and_weight | (intros; apply GlobalTheory.ColClass.classes_and_weight <;> assumption)
