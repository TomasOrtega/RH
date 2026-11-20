import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassOfCharpolyCardCyclicVectors
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FEndomorphismMassOfCharpolyCardCyclicVectors.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.endomorphismMassOfCharpoly_card_cyclic_vectors : ∀ (F : Type) [Field F] [Finite F] (D : F[X]), D.Monic → mass (fun g : Module.End F (Fin D.natDegree → F) => (Nat.card {v : Fin D.natDegree → F // ∀ U : Submodule F (Fin D.natDegree → F), (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤} : ℂ)) D = glCard F D.natDegree := by
  first | exact @GlobalTheory.CuspGL.mass_card_cyclic | exact GlobalTheory.CuspGL.mass_card_cyclic | (intros; apply GlobalTheory.CuspGL.mass_card_cyclic <;> assumption)
