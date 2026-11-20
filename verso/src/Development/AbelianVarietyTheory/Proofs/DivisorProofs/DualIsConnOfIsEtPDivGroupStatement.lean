import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualIsConnOfIsEtPDivGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualIsConnOfIsEtPDivGroup.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.dual_isConn_of_isEt_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → G.dual.IsConn := by
  first | exact @GlobalTheory.PDivGroup.dual_isConn_of_isEt | exact GlobalTheory.PDivGroup.dual_isConn_of_isEt | (intros; apply GlobalTheory.PDivGroup.dual_isConn_of_isEt <;> assumption)
