import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNilpotentResidueToMatrixMulLeft
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsNilpotentResidueToMatrixMulLeft.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.isNilpotent_residue_toMatrix_mulLeft' : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  first | exact @GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | exact GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | (intros; apply GlobalTheory.isNilpotent_residue_toMatrix_mulLeft <;> assumption)
