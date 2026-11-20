import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCartanDecomposition
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCartanDecomposition.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_cartan_decomposition : ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), IsInU ε g → ∃ X, IsCartan ε g X := by
  first | exact @GlobalTheory.CartanExists.exists_isCartan | exact GlobalTheory.CartanExists.exists_isCartan | (intros; apply GlobalTheory.CartanExists.exists_isCartan <;> assumption)
