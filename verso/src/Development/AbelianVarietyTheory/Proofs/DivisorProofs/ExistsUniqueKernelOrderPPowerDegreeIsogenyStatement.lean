import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueKernelOrderPPowerDegreeIsogeny
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dieu.existsUnique_hasLogDeg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUniqueKernelOrderPPowerDegreeIsogeny.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.existsUnique_kernelOrder_pPowerDegree_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q : PDivGroup p k) (q : G ⟶ Q), IsIsog q → ∃! e : ℕ, HasLogDeg q e := by
  first | exact @GlobalTheory.Dieu.existsUnique_hasLogDeg | exact GlobalTheory.Dieu.existsUnique_hasLogDeg | (intros; apply GlobalTheory.Dieu.existsUnique_hasLogDeg <;> assumption)
