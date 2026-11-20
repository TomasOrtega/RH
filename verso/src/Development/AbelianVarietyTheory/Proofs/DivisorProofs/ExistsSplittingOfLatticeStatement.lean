import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplittingOfLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSplittingOfLattice.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_splitting_of_lattice : ∀ (X : Scheme.{0}) [IsIntegral X] (U : AffOp X) (h : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)) (c : U.Bp), (c : Kbar X) ≠ 0 → Module.Finite U.Bp L → Module.Projective U.Bp L → (∀ x : Fin h → U.Bp, c • x ∈ L) → ∃ (n : ℕ) (g : Fin n → Fin h → U.Bp) (S : Fin n → Fin h → Kbar X), Splits U L g S := by
  first | exact @GlobalTheory.BplusDescent.exists_splits | exact GlobalTheory.BplusDescent.exists_splits | (intros; apply GlobalTheory.BplusDescent.exists_splits <;> assumption)
