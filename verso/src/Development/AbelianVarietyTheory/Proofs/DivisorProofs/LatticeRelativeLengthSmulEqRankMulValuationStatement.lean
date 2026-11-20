import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRelativeLengthSmulEqRankMulValuation
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeRelativeLengthSmulEqRankMulValuation.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ), v (c : C) = r → RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  first | exact @GlobalTheory.ScalLen.relLen_map_lsmul | exact GlobalTheory.ScalLen.relLen_map_lsmul | (intros; apply GlobalTheory.ScalLen.relLen_map_lsmul <;> assumption)
