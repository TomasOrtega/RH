import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackDualHomEqZeroOfIsEt
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRigidifiedExtensionPullbackDualHomEqZeroOfIsEt.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_dualHom_eq_zero_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (f : G ⟶ H), G.IsEt → H.IsEt → rigExtMap f = 0 → rigExtMap (dualHom G H f) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt | exact GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt | (intros; apply GlobalTheory.PDivGroup.rigExtMap_dualHom_eq_zero_of_isEt <;> assumption)
