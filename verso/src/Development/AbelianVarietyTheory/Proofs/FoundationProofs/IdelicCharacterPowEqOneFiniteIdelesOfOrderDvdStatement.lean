import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIdelicCharacterPowEqOneFiniteIdelesOfOrderDvd.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  first | exact @GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd | exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd | (intros; apply GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd <;> assumption)
