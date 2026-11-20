import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHeckeCharacterOfUnitaryTensorIdeles.lean&line=186#L186)
-/
theorem _root_.GlobalTheory.T.exists_heckeCharacter_of_unitary_tensorIdeles : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq c χ := by
  first | exact @GlobalTheory.HeckeTensorRead.exists_hchar_chrEq | exact GlobalTheory.HeckeTensorRead.exists_hchar_chrEq | (intros; apply GlobalTheory.HeckeTensorRead.exists_hchar_chrEq <;> assumption)
