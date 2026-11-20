import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGamma
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsEisensteinSlashNeOutsideGamma.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.exists_eisenstein_slash_ne_outside_gamma : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M → ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  first | exact @GlobalTheory.EisSep.exists_isMF_slash_ne | exact GlobalTheory.EisSep.exists_isMF_slash_ne | (intros; apply GlobalTheory.EisSep.exists_isMF_slash_ne <;> assumption)
