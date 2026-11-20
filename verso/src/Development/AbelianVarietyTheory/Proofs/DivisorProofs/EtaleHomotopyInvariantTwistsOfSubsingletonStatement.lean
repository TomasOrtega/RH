import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingleton
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleHomotopyInvariantTwistsOfSubsingleton.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  first | exact @GlobalTheory.EtC.hInv_of_subsingleton | exact GlobalTheory.EtC.hInv_of_subsingleton | (intros; apply GlobalTheory.EtC.hInv_of_subsingleton; all_goals assumption)
