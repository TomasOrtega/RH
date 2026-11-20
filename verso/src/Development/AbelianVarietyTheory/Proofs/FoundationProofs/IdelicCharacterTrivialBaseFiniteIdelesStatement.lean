import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterTrivialBaseFiniteIdeles
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIdelicCharacterTrivialBaseFiniteIdeles.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.idelicCharacter_trivial_baseFiniteIdeles : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → χ.TrivOn D.host.F → ∀ a : (AF D.host.F)ˣ, infPart D (idF D a : AE D) = 1 → c (idF D a) = 1 := by
  first | exact @GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial | exact GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial | (intros; apply GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial <;> assumption)
