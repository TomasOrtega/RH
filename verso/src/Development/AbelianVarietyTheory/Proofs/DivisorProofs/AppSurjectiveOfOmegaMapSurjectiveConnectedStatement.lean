import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAppSurjectiveOfOmegaMapSurjectiveConnected.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.app_surjective_of_omegaMap_surjective_connected : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), G.IsConn → Function.Surjective (omegaMap G H q) → ∀ n, Function.Surjective (q.app n) := by
  first | exact @GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | exact GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective | (intros; apply GlobalTheory.PDivGroup.app_surjective_of_omegaMap_surjective <;> assumption)
