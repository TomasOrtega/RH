import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepCompHomAndMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsCharacterOfFDRepCompHomAndMul.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul : (∀ (G M : Type) [Group G] [Group M] (π : G →* M) (χ : M → ℂ), IsChar χ → IsChar (fun x => χ (π x))) ∧ ∀ (G : Type) [Group G] (α β : G → ℂ), IsChar α → IsChar β → IsChar (fun x => α x * β x) := by
  first | exact @GlobalTheory.GLm.isChar_comp_hom_and_mul | exact GlobalTheory.GLm.isChar_comp_hom_and_mul | (intros; apply GlobalTheory.GLm.isChar_comp_hom_and_mul <;> assumption)
