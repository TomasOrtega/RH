import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomEqZeroOfIsConnOfIsEt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHomEqZeroOfIsConnOfIsEt.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.hom_eq_zero_of_isConn_of_isEt' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k), G.IsConn → H.IsEt → (∀ f : G ⟶ H, f = 0) ∧ ∀ f : H ⟶ G, f = 0 := by
  first | exact @GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt | exact GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.hom_eq_zero_of_isConn_of_isEt <;> assumption)
