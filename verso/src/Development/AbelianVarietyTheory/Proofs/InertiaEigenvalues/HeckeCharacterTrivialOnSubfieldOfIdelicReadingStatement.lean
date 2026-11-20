import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReading
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrivOnRead.trivOn_of_chrEq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHeckeCharacterTrivialOnSubfieldOfIdelicReading.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.heckeCharacter_trivialOnSubfield_of_idelicReading : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  first | exact @GlobalTheory.TrivOnRead.trivOn_of_chrEq | exact GlobalTheory.TrivOnRead.trivOn_of_chrEq | (intros; apply GlobalTheory.TrivOnRead.trivOn_of_chrEq <;> assumption)
