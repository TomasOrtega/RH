import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffOpCoverBasicOpenRefine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteAffOpCoverBasicOpenRefine.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_finite_affine_cover_refining_basicOpens : ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X], ∃ (ι : Type) (_ : Finite ι) (W : ι → AffOp X), ∀ U : AffOp X, ∃ (m : ℕ) (a : Fin m → Γ(X, U.1)) (V : Fin m → AffOp X), Ideal.span (Set.range a) = ⊤ ∧ ∀ k, (V k).1 = X.basicOpen (a k) ∧ ∃ i, (V k).1 ≤ (W i).1 := by
  first | exact @GlobalTheory.exists_finite_affOp_cover_basicOpen_refine | exact GlobalTheory.exists_finite_affOp_cover_basicOpen_refine | (intros; apply GlobalTheory.exists_finite_affOp_cover_basicOpen_refine <;> assumption)
