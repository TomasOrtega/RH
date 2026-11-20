import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionFiniteCommAssocAdd
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FMonicFactorizationConvolutionFiniteCommAssocAdd.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add : ∀ (F : Type) [Field F] (P : F[X]), P.Monic → {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite ∧ ∀ a b c : F[X] → ℂ, conv a b P = conv b a P ∧ conv (conv a b) c P = conv a (conv b c) P ∧ conv (a + b) c P = conv a c P + conv b c P ∧ conv (a - b) c P = conv a c P - conv b c P := by
  first | exact @GlobalTheory.CuspGL.conv_basic | exact GlobalTheory.CuspGL.conv_basic | (intros; apply GlobalTheory.CuspGL.conv_basic <;> assumption)
