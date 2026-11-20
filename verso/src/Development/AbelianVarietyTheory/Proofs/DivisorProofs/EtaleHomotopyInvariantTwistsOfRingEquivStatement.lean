import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfRingEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtC.hInv_of_ringEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleHomotopyInvariantTwistsOfRingEquiv.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv : ∀ (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B], (A ≃+* B) → HInv q A → HInv q B := by
  first | exact @GlobalTheory.EtC.hInv_of_ringEquiv | exact GlobalTheory.EtC.hInv_of_ringEquiv | (intros; apply GlobalTheory.EtC.hInv_of_ringEquiv; all_goals assumption)
