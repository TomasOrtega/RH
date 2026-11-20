import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoIsogenyOmegaAndDualSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsIsoIsogenyOmegaAndDualSurjective.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.isIso_isogeny_omega_and_dual_surjective : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → Function.Surjective (omegaMap G H q) → Function.Surjective (omegaMap H.dual G.dual (dualHom G H q)) → IsIso q := by
  first | exact @GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | exact GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective | (intros; apply GlobalTheory.Dieu.isIso_of_isIsog_of_omegaMap_surjective <;> assumption)
